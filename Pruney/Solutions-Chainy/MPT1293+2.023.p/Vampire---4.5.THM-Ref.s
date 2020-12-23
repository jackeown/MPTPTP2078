%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:20 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  242 ( 783 expanded)
%              Number of leaves         :   52 ( 291 expanded)
%              Depth                    :   10
%              Number of atoms          :  563 (1750 expanded)
%              Number of equality atoms :   76 ( 307 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1443,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f73,f80,f111,f128,f133,f264,f269,f274,f423,f428,f433,f753,f758,f763,f832,f837,f842,f847,f852,f857,f1173,f1196,f1201,f1206,f1211,f1216,f1221,f1240,f1283,f1290,f1295,f1300,f1442])).

fof(f1442,plain,
    ( ~ spl3_10
    | spl3_20
    | ~ spl3_29 ),
    inference(avatar_contradiction_clause,[],[f1441])).

fof(f1441,plain,
    ( $false
    | ~ spl3_10
    | spl3_20
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f1440,f1181])).

fof(f1181,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK1,sK2)))
    | ~ spl3_10
    | spl3_20 ),
    inference(forward_demodulation,[],[f1180,f273])).

fof(f273,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl3_10
  <=> k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f1180,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,sK1)))
    | spl3_20 ),
    inference(forward_demodulation,[],[f1179,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1179,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))
    | spl3_20 ),
    inference(forward_demodulation,[],[f1177,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(f1177,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k2_xboole_0(k3_tarski(sK2),k3_tarski(k4_xboole_0(sK1,sK2))))
    | spl3_20 ),
    inference(unit_resulting_resolution,[],[f846,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f846,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2)))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f844])).

fof(f844,plain,
    ( spl3_20
  <=> r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f1440,plain,
    ( r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK1,sK2)))
    | ~ spl3_29 ),
    inference(unit_resulting_resolution,[],[f1220,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f1220,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f1218])).

fof(f1218,plain,
    ( spl3_29
  <=> r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f1300,plain,
    ( spl3_34
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f215,f65,f1297])).

fof(f1297,plain,
    ( spl3_34
  <=> r1_tarski(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f65,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f215,plain,
    ( r1_tarski(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK2,sK2)))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f214,f81])).

fof(f81,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f67,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f67,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f214,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK2,sK2)))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f196,f115])).

fof(f115,plain,
    ( ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f67,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f196,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK2)))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f67,f67,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

fof(f1295,plain,
    ( spl3_33
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f213,f70,f65,f1292])).

fof(f1292,plain,
    ( spl3_33
  <=> r1_tarski(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f70,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f213,plain,
    ( r1_tarski(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK1,sK2)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f212,f82])).

fof(f82,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f72,f46])).

fof(f72,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f212,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK1,sK2)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f197,f115])).

fof(f197,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f72,f67,f48])).

fof(f1290,plain,
    ( spl3_32
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f211,f70,f65,f1287])).

fof(f1287,plain,
    ( spl3_32
  <=> r1_tarski(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f211,plain,
    ( r1_tarski(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK2,sK1)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f210,f81])).

fof(f210,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK2,sK1)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f198,f116])).

fof(f116,plain,
    ( ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1) = k3_xboole_0(X0,sK1)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f72,f53])).

fof(f198,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f67,f72,f48])).

fof(f1283,plain,
    ( spl3_31
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f209,f70,f1280])).

fof(f1280,plain,
    ( spl3_31
  <=> r1_tarski(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f209,plain,
    ( r1_tarski(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK1,sK1)))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f208,f82])).

fof(f208,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK1,sK1)))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f199,f116])).

fof(f199,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK1)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f72,f72,f48])).

fof(f1240,plain,
    ( spl3_30
    | ~ spl3_2
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f1157,f755,f750,f425,f271,f65,f1237])).

fof(f1237,plain,
    ( spl3_30
  <=> r1_tarski(sK2,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f425,plain,
    ( spl3_12
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f750,plain,
    ( spl3_14
  <=> m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f755,plain,
    ( spl3_15
  <=> m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f1157,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl3_2
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f1156,f93])).

fof(f93,plain,
    ( sK2 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f87,f81])).

fof(f87,plain,
    ( sK2 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f67,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1156,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)),k2_xboole_0(sK1,sK2))
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f1155,f618])).

fof(f618,plain,
    ( k2_xboole_0(sK1,sK2) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2)))
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f527,f526])).

fof(f526,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2)) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2))
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f427,f46])).

fof(f427,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f425])).

fof(f527,plain,
    ( k2_xboole_0(sK1,sK2) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2)))
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f427,f47])).

fof(f1155,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2))))
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f1154,f273])).

fof(f1154,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK2,sK1))))
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f1153,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

fof(f1153,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1))))
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f1009,f880])).

fof(f880,plain,
    ( ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) = k3_xboole_0(X0,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1))
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f752,f53])).

fof(f752,plain,
    ( m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f750])).

fof(f1009,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1))))
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f752,f757,f48])).

fof(f757,plain,
    ( m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f755])).

fof(f1221,plain,
    ( spl3_29
    | ~ spl3_3
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f1134,f755,f750,f425,f70,f1218])).

fof(f1134,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ spl3_3
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f1133,f92])).

fof(f92,plain,
    ( sK1 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f88,f82])).

fof(f88,plain,
    ( sK1 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f72,f47])).

fof(f1133,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k2_xboole_0(sK1,sK2))
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f1132,f618])).

fof(f1132,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2))))
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f1131,f51])).

fof(f1131,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2))))
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f1018,f1026])).

fof(f1026,plain,
    ( ! [X0] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k3_xboole_0(X0,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2))
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f757,f53])).

fof(f1018,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2))))
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f752,f757,f48])).

fof(f1216,plain,
    ( spl3_28
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f93,f65,f1213])).

fof(f1213,plain,
    ( spl3_28
  <=> sK2 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f1211,plain,
    ( spl3_27
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f92,f70,f1208])).

fof(f1208,plain,
    ( spl3_27
  <=> sK1 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f1206,plain,
    ( spl3_26
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f82,f70,f1203])).

fof(f1203,plain,
    ( spl3_26
  <=> k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f1201,plain,
    ( spl3_25
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f81,f65,f1198])).

fof(f1198,plain,
    ( spl3_25
  <=> k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f1196,plain,
    ( spl3_24
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f1130,f755,f430,f65,f1193])).

fof(f1193,plain,
    ( spl3_24
  <=> r1_tarski(sK2,k2_xboole_0(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f430,plain,
    ( spl3_13
  <=> m1_subset_1(k2_xboole_0(sK2,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f1130,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK2,sK2))
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f1129,f93])).

fof(f1129,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)),k2_xboole_0(sK2,sK2))
    | ~ spl3_13
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f1128,f738])).

fof(f738,plain,
    ( k2_xboole_0(sK2,sK2) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK2,sK2)))
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f632,f631])).

fof(f631,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK2,sK2)) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK2,sK2))
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f432,f46])).

fof(f432,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f430])).

fof(f632,plain,
    ( k2_xboole_0(sK2,sK2) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK2,sK2)))
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f432,f47])).

fof(f1128,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK2,sK2))))
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f1127,f51])).

fof(f1127,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2))))
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f1019,f1026])).

fof(f1019,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2))))
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f757,f757,f48])).

fof(f1173,plain,
    ( spl3_23
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f974,f750,f420,f70,f1170])).

fof(f1170,plain,
    ( spl3_23
  <=> r1_tarski(sK1,k2_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f420,plain,
    ( spl3_11
  <=> m1_subset_1(k2_xboole_0(sK1,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f974,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,sK1))
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f973,f92])).

fof(f973,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k2_xboole_0(sK1,sK1))
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f972,f514])).

fof(f514,plain,
    ( k2_xboole_0(sK1,sK1) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK1)))
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f438,f437])).

fof(f437,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK1)) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK1))
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f422,f46])).

fof(f422,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f420])).

fof(f438,plain,
    ( k2_xboole_0(sK1,sK1) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK1)))
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f422,f47])).

fof(f972,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK1))))
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f971,f51])).

fof(f971,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1))))
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f873,f880])).

fof(f873,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1))))
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f752,f752,f48])).

fof(f857,plain,
    ( spl3_22
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f194,f70,f65,f854])).

fof(f854,plain,
    ( spl3_22
  <=> k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f194,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1) = k2_xboole_0(sK1,sK2)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f145,f192])).

fof(f192,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,sK1)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f191,f144])).

fof(f144,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f72,f67,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f191,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k2_xboole_0(sK2,sK1)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f176,f145])).

fof(f176,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f67,f72,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(f145,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1) = k2_xboole_0(sK2,sK1)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f67,f72,f57])).

fof(f852,plain,
    ( spl3_21
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f245,f130,f849])).

fof(f849,plain,
    ( spl3_21
  <=> m1_subset_1(k3_tarski(k2_xboole_0(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f130,plain,
    ( spl3_7
  <=> m1_subset_1(k3_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f245,plain,
    ( m1_subset_1(k3_tarski(k2_xboole_0(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f229,f239])).

fof(f239,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_tarski(sK2),k3_tarski(sK2)) = k3_tarski(k2_xboole_0(sK2,sK2))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f233,f43])).

fof(f233,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_tarski(sK2),k3_tarski(sK2)) = k2_xboole_0(k3_tarski(sK2),k3_tarski(sK2))
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f132,f132,f57])).

fof(f132,plain,
    ( m1_subset_1(k3_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f229,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),k3_tarski(sK2),k3_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f132,f132,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f847,plain,
    ( ~ spl3_20
    | ~ spl3_3
    | ~ spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f168,f125,f108,f70,f844])).

fof(f108,plain,
    ( spl3_5
  <=> m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f125,plain,
    ( spl3_6
  <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f168,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2)))
    | ~ spl3_3
    | ~ spl3_5
    | spl3_6 ),
    inference(backward_demodulation,[],[f137,f158])).

fof(f158,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),X0) = k4_xboole_0(k3_tarski(sK1),X0)
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f110,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f110,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f137,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2)))
    | ~ spl3_3
    | spl3_6 ),
    inference(subsumption_resolution,[],[f135,f122])).

fof(f122,plain,
    ( ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f113,f118])).

fof(f118,plain,
    ( ! [X0] : k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f72,f54])).

fof(f113,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f72,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f135,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_6 ),
    inference(superposition,[],[f127,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f127,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f842,plain,
    ( spl3_19
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f146,f70,f839])).

fof(f839,plain,
    ( spl3_19
  <=> k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK1) = k2_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f146,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK1) = k2_xboole_0(sK1,sK1)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f72,f72,f57])).

fof(f837,plain,
    ( spl3_18
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f144,f70,f65,f834])).

fof(f834,plain,
    ( spl3_18
  <=> k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f832,plain,
    ( spl3_17
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f143,f65,f829])).

fof(f829,plain,
    ( spl3_17
  <=> k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK2) = k2_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f143,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK2) = k2_xboole_0(sK2,sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f67,f67,f57])).

fof(f763,plain,
    ( spl3_16
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f166,f108,f760])).

fof(f760,plain,
    ( spl3_16
  <=> m1_subset_1(k3_tarski(k2_xboole_0(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f166,plain,
    ( m1_subset_1(k3_tarski(k2_xboole_0(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f160,f164])).

fof(f164,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK1)) = k3_tarski(k2_xboole_0(sK1,sK1))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f162,f43])).

fof(f162,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK1)) = k2_xboole_0(k3_tarski(sK1),k3_tarski(sK1))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f110,f110,f57])).

fof(f160,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f110,f110,f56])).

fof(f758,plain,
    ( spl3_15
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f86,f77,f65,f755])).

fof(f77,plain,
    ( spl3_4
  <=> m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f86,plain,
    ( m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f79,f81])).

fof(f79,plain,
    ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f753,plain,
    ( spl3_14
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f85,f70,f750])).

fof(f85,plain,
    ( m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f75,f82])).

fof(f75,plain,
    ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f72,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f433,plain,
    ( spl3_13
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f152,f65,f430])).

fof(f152,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f138,f143])).

fof(f138,plain,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f67,f67,f56])).

fof(f428,plain,
    ( spl3_12
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f151,f70,f65,f425])).

fof(f151,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f139,f144])).

fof(f139,plain,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f72,f67,f56])).

fof(f423,plain,
    ( spl3_11
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f149,f70,f420])).

fof(f149,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f141,f146])).

fof(f141,plain,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f72,f72,f56])).

fof(f274,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f192,f70,f65,f271])).

fof(f269,plain,
    ( spl3_9
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f97,f70,f266])).

fof(f266,plain,
    ( spl3_9
  <=> k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f97,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f72,f49])).

fof(f264,plain,
    ( spl3_8
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f96,f65,f261])).

fof(f261,plain,
    ( spl3_8
  <=> k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f96,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f67,f49])).

fof(f133,plain,
    ( spl3_7
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f106,f65,f130])).

fof(f106,plain,
    ( m1_subset_1(k3_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f100,f96])).

fof(f100,plain,
    ( m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f67,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f128,plain,
    ( ~ spl3_6
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f121,f70,f65,f125])).

fof(f121,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f99,f118])).

fof(f99,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f98,f96])).

fof(f98,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f39,f97])).

fof(f39,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).

fof(f111,plain,
    ( spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f105,f70,f108])).

fof(f105,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f101,f97])).

fof(f101,plain,
    ( m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f72,f50])).

fof(f80,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f74,f65,f77])).

fof(f74,plain,
    ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f67,f45])).

fof(f73,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f40,f70])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f38,f65])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f41,f60])).

fof(f60,plain,
    ( spl3_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f41,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (9621)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.49  % (9607)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.49  % (9603)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.49  % (9609)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.49  % (9605)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.49  % (9602)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.49  % (9601)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.49  % (9602)Refutation not found, incomplete strategy% (9602)------------------------------
% 0.21/0.49  % (9602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (9602)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (9602)Memory used [KB]: 10490
% 0.21/0.49  % (9602)Time elapsed: 0.087 s
% 0.21/0.49  % (9602)------------------------------
% 0.21/0.49  % (9602)------------------------------
% 0.21/0.50  % (9610)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.50  % (9604)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (9606)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (9620)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.50  % (9623)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.50  % (9619)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.50  % (9599)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (9623)Refutation not found, incomplete strategy% (9623)------------------------------
% 0.21/0.51  % (9623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9623)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (9623)Memory used [KB]: 10618
% 0.21/0.51  % (9623)Time elapsed: 0.056 s
% 0.21/0.51  % (9623)------------------------------
% 0.21/0.51  % (9623)------------------------------
% 0.21/0.51  % (9618)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (9614)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (9611)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (9600)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (9612)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.51  % (9613)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.52  % (9608)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.52  % (9622)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.52  % (9617)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % (9615)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 2.13/0.63  % (9622)Refutation not found, incomplete strategy% (9622)------------------------------
% 2.13/0.63  % (9622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.63  % (9622)Termination reason: Refutation not found, incomplete strategy
% 2.13/0.63  
% 2.13/0.63  % (9622)Memory used [KB]: 1535
% 2.13/0.63  % (9622)Time elapsed: 0.196 s
% 2.13/0.63  % (9622)------------------------------
% 2.13/0.63  % (9622)------------------------------
% 2.13/0.63  % (9614)Refutation found. Thanks to Tanya!
% 2.13/0.63  % SZS status Theorem for theBenchmark
% 2.13/0.64  % SZS output start Proof for theBenchmark
% 2.13/0.64  fof(f1443,plain,(
% 2.13/0.64    $false),
% 2.13/0.64    inference(avatar_sat_refutation,[],[f63,f68,f73,f80,f111,f128,f133,f264,f269,f274,f423,f428,f433,f753,f758,f763,f832,f837,f842,f847,f852,f857,f1173,f1196,f1201,f1206,f1211,f1216,f1221,f1240,f1283,f1290,f1295,f1300,f1442])).
% 2.13/0.64  fof(f1442,plain,(
% 2.13/0.64    ~spl3_10 | spl3_20 | ~spl3_29),
% 2.13/0.64    inference(avatar_contradiction_clause,[],[f1441])).
% 2.13/0.64  fof(f1441,plain,(
% 2.13/0.64    $false | (~spl3_10 | spl3_20 | ~spl3_29)),
% 2.13/0.64    inference(subsumption_resolution,[],[f1440,f1181])).
% 2.13/0.64  fof(f1181,plain,(
% 2.13/0.64    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK1,sK2))) | (~spl3_10 | spl3_20)),
% 2.13/0.64    inference(forward_demodulation,[],[f1180,f273])).
% 2.13/0.64  fof(f273,plain,(
% 2.13/0.64    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,sK1) | ~spl3_10),
% 2.13/0.64    inference(avatar_component_clause,[],[f271])).
% 2.13/0.64  fof(f271,plain,(
% 2.13/0.64    spl3_10 <=> k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,sK1)),
% 2.13/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.13/0.64  fof(f1180,plain,(
% 2.13/0.64    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,sK1))) | spl3_20),
% 2.13/0.64    inference(forward_demodulation,[],[f1179,f42])).
% 2.13/0.64  fof(f42,plain,(
% 2.13/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.13/0.64    inference(cnf_transformation,[],[f1])).
% 2.13/0.64  fof(f1,axiom,(
% 2.13/0.64    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.13/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.13/0.64  fof(f1179,plain,(
% 2.13/0.64    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) | spl3_20),
% 2.13/0.64    inference(forward_demodulation,[],[f1177,f43])).
% 2.13/0.64  fof(f43,plain,(
% 2.13/0.64    ( ! [X0,X1] : (k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))) )),
% 2.13/0.64    inference(cnf_transformation,[],[f5])).
% 2.13/0.64  fof(f5,axiom,(
% 2.13/0.64    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 2.13/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).
% 2.13/0.64  fof(f1177,plain,(
% 2.13/0.64    ~r1_tarski(k3_tarski(sK1),k2_xboole_0(k3_tarski(sK2),k3_tarski(k4_xboole_0(sK1,sK2)))) | spl3_20),
% 2.13/0.64    inference(unit_resulting_resolution,[],[f846,f55])).
% 2.13/0.64  fof(f55,plain,(
% 2.13/0.64    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.13/0.64    inference(cnf_transformation,[],[f31])).
% 2.13/0.64  fof(f31,plain,(
% 2.13/0.64    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.13/0.64    inference(ennf_transformation,[],[f2])).
% 2.13/0.64  fof(f2,axiom,(
% 2.13/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.13/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.13/0.64  fof(f846,plain,(
% 2.13/0.64    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) | spl3_20),
% 2.13/0.64    inference(avatar_component_clause,[],[f844])).
% 2.13/0.64  fof(f844,plain,(
% 2.13/0.64    spl3_20 <=> r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2)))),
% 2.13/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 2.13/0.64  fof(f1440,plain,(
% 2.13/0.64    r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK1,sK2))) | ~spl3_29),
% 2.13/0.64    inference(unit_resulting_resolution,[],[f1220,f44])).
% 2.13/0.64  fof(f44,plain,(
% 2.13/0.64    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 2.13/0.64    inference(cnf_transformation,[],[f21])).
% 2.13/0.64  fof(f21,plain,(
% 2.13/0.64    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 2.13/0.64    inference(ennf_transformation,[],[f4])).
% 2.13/0.64  fof(f4,axiom,(
% 2.13/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 2.13/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 2.13/0.64  fof(f1220,plain,(
% 2.13/0.64    r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | ~spl3_29),
% 2.13/0.64    inference(avatar_component_clause,[],[f1218])).
% 2.13/0.64  fof(f1218,plain,(
% 2.13/0.64    spl3_29 <=> r1_tarski(sK1,k2_xboole_0(sK1,sK2))),
% 2.13/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 2.13/0.64  fof(f1300,plain,(
% 2.13/0.64    spl3_34 | ~spl3_2),
% 2.13/0.64    inference(avatar_split_clause,[],[f215,f65,f1297])).
% 2.13/0.64  fof(f1297,plain,(
% 2.13/0.64    spl3_34 <=> r1_tarski(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK2,sK2)))),
% 2.13/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 2.13/0.64  fof(f65,plain,(
% 2.13/0.64    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.13/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.13/0.64  fof(f215,plain,(
% 2.13/0.64    r1_tarski(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK2,sK2))) | ~spl3_2),
% 2.13/0.64    inference(forward_demodulation,[],[f214,f81])).
% 2.13/0.64  fof(f81,plain,(
% 2.13/0.64    k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2) | ~spl3_2),
% 2.13/0.64    inference(unit_resulting_resolution,[],[f67,f46])).
% 2.13/0.64  fof(f46,plain,(
% 2.13/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.13/0.64    inference(cnf_transformation,[],[f23])).
% 2.13/0.64  fof(f23,plain,(
% 2.13/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.64    inference(ennf_transformation,[],[f7])).
% 2.13/0.64  fof(f7,axiom,(
% 2.13/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.13/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.13/0.64  fof(f67,plain,(
% 2.13/0.64    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_2),
% 2.13/0.64    inference(avatar_component_clause,[],[f65])).
% 2.13/0.64  fof(f214,plain,(
% 2.13/0.64    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK2,sK2))) | ~spl3_2),
% 2.13/0.64    inference(forward_demodulation,[],[f196,f115])).
% 2.13/0.64  fof(f115,plain,(
% 2.13/0.64    ( ! [X0] : (k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK2) = k3_xboole_0(X0,sK2)) ) | ~spl3_2),
% 2.13/0.64    inference(unit_resulting_resolution,[],[f67,f53])).
% 2.13/0.64  fof(f53,plain,(
% 2.13/0.64    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.13/0.64    inference(cnf_transformation,[],[f29])).
% 2.13/0.64  fof(f29,plain,(
% 2.13/0.64    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.13/0.64    inference(ennf_transformation,[],[f14])).
% 2.13/0.64  fof(f14,axiom,(
% 2.13/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.13/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.13/0.64  fof(f196,plain,(
% 2.13/0.64    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK2))) | ~spl3_2),
% 2.13/0.64    inference(unit_resulting_resolution,[],[f67,f67,f48])).
% 2.13/0.64  fof(f48,plain,(
% 2.13/0.64    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.13/0.64    inference(cnf_transformation,[],[f25])).
% 2.13/0.64  fof(f25,plain,(
% 2.13/0.64    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.64    inference(ennf_transformation,[],[f15])).
% 2.13/0.64  fof(f15,axiom,(
% 2.13/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 2.13/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).
% 2.13/0.64  fof(f1295,plain,(
% 2.13/0.64    spl3_33 | ~spl3_2 | ~spl3_3),
% 2.13/0.64    inference(avatar_split_clause,[],[f213,f70,f65,f1292])).
% 2.13/0.64  fof(f1292,plain,(
% 2.13/0.64    spl3_33 <=> r1_tarski(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK1,sK2)))),
% 2.13/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 2.13/0.64  fof(f70,plain,(
% 2.13/0.64    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.13/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.13/0.64  fof(f213,plain,(
% 2.13/0.64    r1_tarski(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK1,sK2))) | (~spl3_2 | ~spl3_3)),
% 2.13/0.64    inference(forward_demodulation,[],[f212,f82])).
% 2.13/0.64  fof(f82,plain,(
% 2.13/0.64    k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1) | ~spl3_3),
% 2.13/0.64    inference(unit_resulting_resolution,[],[f72,f46])).
% 2.13/0.64  fof(f72,plain,(
% 2.13/0.64    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_3),
% 2.13/0.64    inference(avatar_component_clause,[],[f70])).
% 2.13/0.64  fof(f212,plain,(
% 2.13/0.64    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK1,sK2))) | (~spl3_2 | ~spl3_3)),
% 2.13/0.64    inference(forward_demodulation,[],[f197,f115])).
% 2.13/0.64  fof(f197,plain,(
% 2.13/0.64    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) | (~spl3_2 | ~spl3_3)),
% 2.13/0.64    inference(unit_resulting_resolution,[],[f72,f67,f48])).
% 2.13/0.64  fof(f1290,plain,(
% 2.13/0.64    spl3_32 | ~spl3_2 | ~spl3_3),
% 2.13/0.64    inference(avatar_split_clause,[],[f211,f70,f65,f1287])).
% 2.13/0.64  fof(f1287,plain,(
% 2.13/0.64    spl3_32 <=> r1_tarski(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK2,sK1)))),
% 2.13/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 2.13/0.64  fof(f211,plain,(
% 2.13/0.64    r1_tarski(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK2,sK1))) | (~spl3_2 | ~spl3_3)),
% 2.13/0.64    inference(forward_demodulation,[],[f210,f81])).
% 2.13/0.64  fof(f210,plain,(
% 2.13/0.64    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK2,sK1))) | (~spl3_2 | ~spl3_3)),
% 2.13/0.64    inference(forward_demodulation,[],[f198,f116])).
% 2.13/0.64  fof(f116,plain,(
% 2.13/0.64    ( ! [X0] : (k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,sK1) = k3_xboole_0(X0,sK1)) ) | ~spl3_3),
% 2.13/0.64    inference(unit_resulting_resolution,[],[f72,f53])).
% 2.13/0.64  fof(f198,plain,(
% 2.13/0.64    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1))) | (~spl3_2 | ~spl3_3)),
% 2.13/0.64    inference(unit_resulting_resolution,[],[f67,f72,f48])).
% 2.13/0.64  fof(f1283,plain,(
% 2.13/0.64    spl3_31 | ~spl3_3),
% 2.13/0.64    inference(avatar_split_clause,[],[f209,f70,f1280])).
% 2.13/0.64  fof(f1280,plain,(
% 2.13/0.64    spl3_31 <=> r1_tarski(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK1,sK1)))),
% 2.13/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 2.13/0.64  fof(f209,plain,(
% 2.13/0.64    r1_tarski(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK1,sK1))) | ~spl3_3),
% 2.13/0.64    inference(forward_demodulation,[],[f208,f82])).
% 2.13/0.64  fof(f208,plain,(
% 2.13/0.64    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(sK1,sK1))) | ~spl3_3),
% 2.13/0.64    inference(forward_demodulation,[],[f199,f116])).
% 2.13/0.64  fof(f199,plain,(
% 2.13/0.64    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK1))) | ~spl3_3),
% 2.13/0.64    inference(unit_resulting_resolution,[],[f72,f72,f48])).
% 2.13/0.64  fof(f1240,plain,(
% 2.13/0.64    spl3_30 | ~spl3_2 | ~spl3_10 | ~spl3_12 | ~spl3_14 | ~spl3_15),
% 2.13/0.64    inference(avatar_split_clause,[],[f1157,f755,f750,f425,f271,f65,f1237])).
% 2.13/0.64  fof(f1237,plain,(
% 2.13/0.64    spl3_30 <=> r1_tarski(sK2,k2_xboole_0(sK1,sK2))),
% 2.13/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 2.13/0.64  fof(f425,plain,(
% 2.13/0.64    spl3_12 <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.13/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 2.13/0.64  fof(f750,plain,(
% 2.13/0.64    spl3_14 <=> m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.13/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.13/0.64  fof(f755,plain,(
% 2.13/0.64    spl3_15 <=> m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.13/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 2.13/0.64  fof(f1157,plain,(
% 2.13/0.64    r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | (~spl3_2 | ~spl3_10 | ~spl3_12 | ~spl3_14 | ~spl3_15)),
% 2.13/0.64    inference(forward_demodulation,[],[f1156,f93])).
% 2.13/0.64  fof(f93,plain,(
% 2.13/0.64    sK2 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) | ~spl3_2),
% 2.13/0.64    inference(forward_demodulation,[],[f87,f81])).
% 2.13/0.64  fof(f87,plain,(
% 2.13/0.64    sK2 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) | ~spl3_2),
% 2.13/0.64    inference(unit_resulting_resolution,[],[f67,f47])).
% 2.13/0.64  fof(f47,plain,(
% 2.13/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.13/0.64    inference(cnf_transformation,[],[f24])).
% 2.13/0.64  fof(f24,plain,(
% 2.13/0.64    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.64    inference(ennf_transformation,[],[f11])).
% 2.13/0.64  fof(f11,axiom,(
% 2.13/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.13/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.13/0.64  fof(f1156,plain,(
% 2.13/0.64    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)),k2_xboole_0(sK1,sK2)) | (~spl3_10 | ~spl3_12 | ~spl3_14 | ~spl3_15)),
% 2.13/0.64    inference(forward_demodulation,[],[f1155,f618])).
% 2.13/0.64  fof(f618,plain,(
% 2.13/0.64    k2_xboole_0(sK1,sK2) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2))) | ~spl3_12),
% 2.13/0.64    inference(backward_demodulation,[],[f527,f526])).
% 2.13/0.64  fof(f526,plain,(
% 2.13/0.64    k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2)) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2)) | ~spl3_12),
% 2.13/0.64    inference(unit_resulting_resolution,[],[f427,f46])).
% 2.13/0.64  fof(f427,plain,(
% 2.13/0.64    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_12),
% 2.13/0.64    inference(avatar_component_clause,[],[f425])).
% 2.13/0.64  fof(f527,plain,(
% 2.13/0.64    k2_xboole_0(sK1,sK2) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2))) | ~spl3_12),
% 2.13/0.64    inference(unit_resulting_resolution,[],[f427,f47])).
% 2.13/0.64  fof(f1155,plain,(
% 2.13/0.64    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2)))) | (~spl3_10 | ~spl3_14 | ~spl3_15)),
% 2.13/0.64    inference(forward_demodulation,[],[f1154,f273])).
% 2.13/0.64  fof(f1154,plain,(
% 2.13/0.64    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK2,sK1)))) | (~spl3_14 | ~spl3_15)),
% 2.13/0.64    inference(forward_demodulation,[],[f1153,f51])).
% 2.13/0.64  fof(f51,plain,(
% 2.13/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 2.13/0.64    inference(cnf_transformation,[],[f3])).
% 2.13/0.64  fof(f3,axiom,(
% 2.13/0.64    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 2.13/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).
% 2.13/0.64  fof(f1153,plain,(
% 2.13/0.64    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)))) | (~spl3_14 | ~spl3_15)),
% 2.13/0.64    inference(forward_demodulation,[],[f1009,f880])).
% 2.13/0.64  fof(f880,plain,(
% 2.13/0.64    ( ! [X0] : (k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) = k3_xboole_0(X0,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1))) ) | ~spl3_14),
% 2.13/0.64    inference(unit_resulting_resolution,[],[f752,f53])).
% 2.13/0.64  fof(f752,plain,(
% 2.13/0.64    m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_14),
% 2.13/0.64    inference(avatar_component_clause,[],[f750])).
% 2.13/0.64  fof(f1009,plain,(
% 2.13/0.64    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)))) | (~spl3_14 | ~spl3_15)),
% 2.13/0.64    inference(unit_resulting_resolution,[],[f752,f757,f48])).
% 2.13/0.64  fof(f757,plain,(
% 2.13/0.64    m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_15),
% 2.13/0.64    inference(avatar_component_clause,[],[f755])).
% 2.13/0.64  fof(f1221,plain,(
% 2.13/0.64    spl3_29 | ~spl3_3 | ~spl3_12 | ~spl3_14 | ~spl3_15),
% 2.13/0.64    inference(avatar_split_clause,[],[f1134,f755,f750,f425,f70,f1218])).
% 2.13/0.64  fof(f1134,plain,(
% 2.13/0.64    r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | (~spl3_3 | ~spl3_12 | ~spl3_14 | ~spl3_15)),
% 2.13/0.64    inference(forward_demodulation,[],[f1133,f92])).
% 2.13/0.64  fof(f92,plain,(
% 2.13/0.64    sK1 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) | ~spl3_3),
% 2.13/0.64    inference(forward_demodulation,[],[f88,f82])).
% 2.13/0.64  fof(f88,plain,(
% 2.13/0.64    sK1 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) | ~spl3_3),
% 2.13/0.64    inference(unit_resulting_resolution,[],[f72,f47])).
% 2.13/0.64  fof(f1133,plain,(
% 2.13/0.64    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k2_xboole_0(sK1,sK2)) | (~spl3_12 | ~spl3_14 | ~spl3_15)),
% 2.13/0.64    inference(forward_demodulation,[],[f1132,f618])).
% 2.13/0.64  fof(f1132,plain,(
% 2.13/0.64    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK2)))) | (~spl3_14 | ~spl3_15)),
% 2.13/0.64    inference(forward_demodulation,[],[f1131,f51])).
% 2.13/0.64  fof(f1131,plain,(
% 2.13/0.64    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)))) | (~spl3_14 | ~spl3_15)),
% 2.13/0.64    inference(forward_demodulation,[],[f1018,f1026])).
% 2.13/0.64  fof(f1026,plain,(
% 2.13/0.64    ( ! [X0] : (k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k3_xboole_0(X0,k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2))) ) | ~spl3_15),
% 2.13/0.64    inference(unit_resulting_resolution,[],[f757,f53])).
% 2.13/0.65  fof(f1018,plain,(
% 2.13/0.65    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)))) | (~spl3_14 | ~spl3_15)),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f752,f757,f48])).
% 2.13/0.65  fof(f1216,plain,(
% 2.13/0.65    spl3_28 | ~spl3_2),
% 2.13/0.65    inference(avatar_split_clause,[],[f93,f65,f1213])).
% 2.13/0.65  fof(f1213,plain,(
% 2.13/0.65    spl3_28 <=> sK2 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 2.13/0.65  fof(f1211,plain,(
% 2.13/0.65    spl3_27 | ~spl3_3),
% 2.13/0.65    inference(avatar_split_clause,[],[f92,f70,f1208])).
% 2.13/0.65  fof(f1208,plain,(
% 2.13/0.65    spl3_27 <=> sK1 = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 2.13/0.65  fof(f1206,plain,(
% 2.13/0.65    spl3_26 | ~spl3_3),
% 2.13/0.65    inference(avatar_split_clause,[],[f82,f70,f1203])).
% 2.13/0.65  fof(f1203,plain,(
% 2.13/0.65    spl3_26 <=> k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 2.13/0.65  fof(f1201,plain,(
% 2.13/0.65    spl3_25 | ~spl3_2),
% 2.13/0.65    inference(avatar_split_clause,[],[f81,f65,f1198])).
% 2.13/0.65  fof(f1198,plain,(
% 2.13/0.65    spl3_25 <=> k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 2.13/0.65  fof(f1196,plain,(
% 2.13/0.65    spl3_24 | ~spl3_2 | ~spl3_13 | ~spl3_15),
% 2.13/0.65    inference(avatar_split_clause,[],[f1130,f755,f430,f65,f1193])).
% 2.13/0.65  fof(f1193,plain,(
% 2.13/0.65    spl3_24 <=> r1_tarski(sK2,k2_xboole_0(sK2,sK2))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 2.13/0.65  fof(f430,plain,(
% 2.13/0.65    spl3_13 <=> m1_subset_1(k2_xboole_0(sK2,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.13/0.65  fof(f1130,plain,(
% 2.13/0.65    r1_tarski(sK2,k2_xboole_0(sK2,sK2)) | (~spl3_2 | ~spl3_13 | ~spl3_15)),
% 2.13/0.65    inference(forward_demodulation,[],[f1129,f93])).
% 2.13/0.65  fof(f1129,plain,(
% 2.13/0.65    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)),k2_xboole_0(sK2,sK2)) | (~spl3_13 | ~spl3_15)),
% 2.13/0.65    inference(forward_demodulation,[],[f1128,f738])).
% 2.13/0.65  fof(f738,plain,(
% 2.13/0.65    k2_xboole_0(sK2,sK2) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK2,sK2))) | ~spl3_13),
% 2.13/0.65    inference(backward_demodulation,[],[f632,f631])).
% 2.13/0.65  fof(f631,plain,(
% 2.13/0.65    k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK2,sK2)) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK2,sK2)) | ~spl3_13),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f432,f46])).
% 2.13/0.65  fof(f432,plain,(
% 2.13/0.65    m1_subset_1(k2_xboole_0(sK2,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_13),
% 2.13/0.65    inference(avatar_component_clause,[],[f430])).
% 2.13/0.65  fof(f632,plain,(
% 2.13/0.65    k2_xboole_0(sK2,sK2) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK2,sK2))) | ~spl3_13),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f432,f47])).
% 2.13/0.65  fof(f1128,plain,(
% 2.13/0.65    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK2,sK2)))) | ~spl3_15),
% 2.13/0.65    inference(forward_demodulation,[],[f1127,f51])).
% 2.13/0.65  fof(f1127,plain,(
% 2.13/0.65    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)))) | ~spl3_15),
% 2.13/0.65    inference(forward_demodulation,[],[f1019,f1026])).
% 2.13/0.65  fof(f1019,plain,(
% 2.13/0.65    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2)))) | ~spl3_15),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f757,f757,f48])).
% 2.13/0.65  fof(f1173,plain,(
% 2.13/0.65    spl3_23 | ~spl3_3 | ~spl3_11 | ~spl3_14),
% 2.13/0.65    inference(avatar_split_clause,[],[f974,f750,f420,f70,f1170])).
% 2.13/0.65  fof(f1170,plain,(
% 2.13/0.65    spl3_23 <=> r1_tarski(sK1,k2_xboole_0(sK1,sK1))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 2.13/0.65  fof(f420,plain,(
% 2.13/0.65    spl3_11 <=> m1_subset_1(k2_xboole_0(sK1,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 2.13/0.65  fof(f974,plain,(
% 2.13/0.65    r1_tarski(sK1,k2_xboole_0(sK1,sK1)) | (~spl3_3 | ~spl3_11 | ~spl3_14)),
% 2.13/0.65    inference(forward_demodulation,[],[f973,f92])).
% 2.13/0.65  fof(f973,plain,(
% 2.13/0.65    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k2_xboole_0(sK1,sK1)) | (~spl3_11 | ~spl3_14)),
% 2.13/0.65    inference(forward_demodulation,[],[f972,f514])).
% 2.13/0.65  fof(f514,plain,(
% 2.13/0.65    k2_xboole_0(sK1,sK1) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK1))) | ~spl3_11),
% 2.13/0.65    inference(backward_demodulation,[],[f438,f437])).
% 2.13/0.65  fof(f437,plain,(
% 2.13/0.65    k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK1)) = k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK1)) | ~spl3_11),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f422,f46])).
% 2.13/0.65  fof(f422,plain,(
% 2.13/0.65    m1_subset_1(k2_xboole_0(sK1,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_11),
% 2.13/0.65    inference(avatar_component_clause,[],[f420])).
% 2.13/0.65  fof(f438,plain,(
% 2.13/0.65    k2_xboole_0(sK1,sK1) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK1))) | ~spl3_11),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f422,f47])).
% 2.13/0.65  fof(f972,plain,(
% 2.13/0.65    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),k2_xboole_0(sK1,sK1)))) | ~spl3_14),
% 2.13/0.65    inference(forward_demodulation,[],[f971,f51])).
% 2.13/0.65  fof(f971,plain,(
% 2.13/0.65    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_xboole_0(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)))) | ~spl3_14),
% 2.13/0.65    inference(forward_demodulation,[],[f873,f880])).
% 2.13/0.65  fof(f873,plain,(
% 2.13/0.65    r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1)))) | ~spl3_14),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f752,f752,f48])).
% 2.13/0.65  fof(f857,plain,(
% 2.13/0.65    spl3_22 | ~spl3_2 | ~spl3_3),
% 2.13/0.65    inference(avatar_split_clause,[],[f194,f70,f65,f854])).
% 2.13/0.65  fof(f854,plain,(
% 2.13/0.65    spl3_22 <=> k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1) = k2_xboole_0(sK1,sK2)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 2.13/0.65  fof(f194,plain,(
% 2.13/0.65    k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1) = k2_xboole_0(sK1,sK2) | (~spl3_2 | ~spl3_3)),
% 2.13/0.65    inference(backward_demodulation,[],[f145,f192])).
% 2.13/0.65  fof(f192,plain,(
% 2.13/0.65    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,sK1) | (~spl3_2 | ~spl3_3)),
% 2.13/0.65    inference(forward_demodulation,[],[f191,f144])).
% 2.13/0.65  fof(f144,plain,(
% 2.13/0.65    k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2) | (~spl3_2 | ~spl3_3)),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f72,f67,f57])).
% 2.13/0.65  fof(f57,plain,(
% 2.13/0.65    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.13/0.65    inference(cnf_transformation,[],[f35])).
% 2.13/0.65  fof(f35,plain,(
% 2.13/0.65    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.65    inference(flattening,[],[f34])).
% 2.13/0.65  fof(f34,plain,(
% 2.13/0.65    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.13/0.65    inference(ennf_transformation,[],[f12])).
% 2.13/0.65  fof(f12,axiom,(
% 2.13/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.13/0.65  fof(f191,plain,(
% 2.13/0.65    k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k2_xboole_0(sK2,sK1) | (~spl3_2 | ~spl3_3)),
% 2.13/0.65    inference(forward_demodulation,[],[f176,f145])).
% 2.13/0.65  fof(f176,plain,(
% 2.13/0.65    k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1) | (~spl3_2 | ~spl3_3)),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f67,f72,f58])).
% 2.13/0.65  fof(f58,plain,(
% 2.13/0.65    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.13/0.65    inference(cnf_transformation,[],[f37])).
% 2.13/0.65  fof(f37,plain,(
% 2.13/0.65    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.65    inference(flattening,[],[f36])).
% 2.13/0.65  fof(f36,plain,(
% 2.13/0.65    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.13/0.65    inference(ennf_transformation,[],[f6])).
% 2.13/0.65  fof(f6,axiom,(
% 2.13/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 2.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).
% 2.13/0.65  fof(f145,plain,(
% 2.13/0.65    k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK1) = k2_xboole_0(sK2,sK1) | (~spl3_2 | ~spl3_3)),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f67,f72,f57])).
% 2.13/0.65  fof(f852,plain,(
% 2.13/0.65    spl3_21 | ~spl3_7),
% 2.13/0.65    inference(avatar_split_clause,[],[f245,f130,f849])).
% 2.13/0.65  fof(f849,plain,(
% 2.13/0.65    spl3_21 <=> m1_subset_1(k3_tarski(k2_xboole_0(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 2.13/0.65  fof(f130,plain,(
% 2.13/0.65    spl3_7 <=> m1_subset_1(k3_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.13/0.65  fof(f245,plain,(
% 2.13/0.65    m1_subset_1(k3_tarski(k2_xboole_0(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_7),
% 2.13/0.65    inference(forward_demodulation,[],[f229,f239])).
% 2.13/0.65  fof(f239,plain,(
% 2.13/0.65    k4_subset_1(u1_struct_0(sK0),k3_tarski(sK2),k3_tarski(sK2)) = k3_tarski(k2_xboole_0(sK2,sK2)) | ~spl3_7),
% 2.13/0.65    inference(forward_demodulation,[],[f233,f43])).
% 2.13/0.65  fof(f233,plain,(
% 2.13/0.65    k4_subset_1(u1_struct_0(sK0),k3_tarski(sK2),k3_tarski(sK2)) = k2_xboole_0(k3_tarski(sK2),k3_tarski(sK2)) | ~spl3_7),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f132,f132,f57])).
% 2.13/0.65  fof(f132,plain,(
% 2.13/0.65    m1_subset_1(k3_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_7),
% 2.13/0.65    inference(avatar_component_clause,[],[f130])).
% 2.13/0.65  fof(f229,plain,(
% 2.13/0.65    m1_subset_1(k4_subset_1(u1_struct_0(sK0),k3_tarski(sK2),k3_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_7),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f132,f132,f56])).
% 2.13/0.65  fof(f56,plain,(
% 2.13/0.65    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.13/0.65    inference(cnf_transformation,[],[f33])).
% 2.13/0.65  fof(f33,plain,(
% 2.13/0.65    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.65    inference(flattening,[],[f32])).
% 2.13/0.65  fof(f32,plain,(
% 2.13/0.65    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.13/0.65    inference(ennf_transformation,[],[f9])).
% 2.13/0.65  fof(f9,axiom,(
% 2.13/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 2.13/0.65  fof(f847,plain,(
% 2.13/0.65    ~spl3_20 | ~spl3_3 | ~spl3_5 | spl3_6),
% 2.13/0.65    inference(avatar_split_clause,[],[f168,f125,f108,f70,f844])).
% 2.13/0.65  fof(f108,plain,(
% 2.13/0.65    spl3_5 <=> m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.13/0.65  fof(f125,plain,(
% 2.13/0.65    spl3_6 <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.13/0.65  fof(f168,plain,(
% 2.13/0.65    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) | (~spl3_3 | ~spl3_5 | spl3_6)),
% 2.13/0.65    inference(backward_demodulation,[],[f137,f158])).
% 2.13/0.65  fof(f158,plain,(
% 2.13/0.65    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),X0) = k4_xboole_0(k3_tarski(sK1),X0)) ) | ~spl3_5),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f110,f54])).
% 2.13/0.65  fof(f54,plain,(
% 2.13/0.65    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.13/0.65    inference(cnf_transformation,[],[f30])).
% 2.13/0.65  fof(f30,plain,(
% 2.13/0.65    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.65    inference(ennf_transformation,[],[f13])).
% 2.13/0.65  fof(f13,axiom,(
% 2.13/0.65    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.13/0.65  fof(f110,plain,(
% 2.13/0.65    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 2.13/0.65    inference(avatar_component_clause,[],[f108])).
% 2.13/0.65  fof(f137,plain,(
% 2.13/0.65    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) | (~spl3_3 | spl3_6)),
% 2.13/0.65    inference(subsumption_resolution,[],[f135,f122])).
% 2.13/0.65  fof(f122,plain,(
% 2.13/0.65    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_3),
% 2.13/0.65    inference(backward_demodulation,[],[f113,f118])).
% 2.13/0.65  fof(f118,plain,(
% 2.13/0.65    ( ! [X0] : (k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k4_xboole_0(sK1,X0)) ) | ~spl3_3),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f72,f54])).
% 2.13/0.65  fof(f113,plain,(
% 2.13/0.65    ( ! [X0] : (m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_3),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f72,f52])).
% 2.13/0.65  fof(f52,plain,(
% 2.13/0.65    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.13/0.65    inference(cnf_transformation,[],[f28])).
% 2.13/0.65  fof(f28,plain,(
% 2.13/0.65    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.65    inference(ennf_transformation,[],[f10])).
% 2.13/0.65  fof(f10,axiom,(
% 2.13/0.65    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 2.13/0.65  fof(f135,plain,(
% 2.13/0.65    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) | ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_6),
% 2.13/0.65    inference(superposition,[],[f127,f49])).
% 2.13/0.65  fof(f49,plain,(
% 2.13/0.65    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.13/0.65    inference(cnf_transformation,[],[f26])).
% 2.13/0.65  fof(f26,plain,(
% 2.13/0.65    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.13/0.65    inference(ennf_transformation,[],[f17])).
% 2.13/0.65  fof(f17,axiom,(
% 2.13/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 2.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 2.13/0.65  fof(f127,plain,(
% 2.13/0.65    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | spl3_6),
% 2.13/0.65    inference(avatar_component_clause,[],[f125])).
% 2.13/0.65  fof(f842,plain,(
% 2.13/0.65    spl3_19 | ~spl3_3),
% 2.13/0.65    inference(avatar_split_clause,[],[f146,f70,f839])).
% 2.13/0.65  fof(f839,plain,(
% 2.13/0.65    spl3_19 <=> k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK1) = k2_xboole_0(sK1,sK1)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 2.13/0.65  fof(f146,plain,(
% 2.13/0.65    k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK1) = k2_xboole_0(sK1,sK1) | ~spl3_3),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f72,f72,f57])).
% 2.13/0.65  fof(f837,plain,(
% 2.13/0.65    spl3_18 | ~spl3_2 | ~spl3_3),
% 2.13/0.65    inference(avatar_split_clause,[],[f144,f70,f65,f834])).
% 2.13/0.65  fof(f834,plain,(
% 2.13/0.65    spl3_18 <=> k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 2.13/0.65  fof(f832,plain,(
% 2.13/0.65    spl3_17 | ~spl3_2),
% 2.13/0.65    inference(avatar_split_clause,[],[f143,f65,f829])).
% 2.13/0.65  fof(f829,plain,(
% 2.13/0.65    spl3_17 <=> k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK2) = k2_xboole_0(sK2,sK2)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 2.13/0.65  fof(f143,plain,(
% 2.13/0.65    k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK2) = k2_xboole_0(sK2,sK2) | ~spl3_2),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f67,f67,f57])).
% 2.13/0.65  fof(f763,plain,(
% 2.13/0.65    spl3_16 | ~spl3_5),
% 2.13/0.65    inference(avatar_split_clause,[],[f166,f108,f760])).
% 2.13/0.65  fof(f760,plain,(
% 2.13/0.65    spl3_16 <=> m1_subset_1(k3_tarski(k2_xboole_0(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 2.13/0.65  fof(f166,plain,(
% 2.13/0.65    m1_subset_1(k3_tarski(k2_xboole_0(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 2.13/0.65    inference(forward_demodulation,[],[f160,f164])).
% 2.13/0.65  fof(f164,plain,(
% 2.13/0.65    k4_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK1)) = k3_tarski(k2_xboole_0(sK1,sK1)) | ~spl3_5),
% 2.13/0.65    inference(forward_demodulation,[],[f162,f43])).
% 2.13/0.65  fof(f162,plain,(
% 2.13/0.65    k4_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK1)) = k2_xboole_0(k3_tarski(sK1),k3_tarski(sK1)) | ~spl3_5),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f110,f110,f57])).
% 2.13/0.65  fof(f160,plain,(
% 2.13/0.65    m1_subset_1(k4_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f110,f110,f56])).
% 2.13/0.65  fof(f758,plain,(
% 2.13/0.65    spl3_15 | ~spl3_2 | ~spl3_4),
% 2.13/0.65    inference(avatar_split_clause,[],[f86,f77,f65,f755])).
% 2.13/0.65  fof(f77,plain,(
% 2.13/0.65    spl3_4 <=> m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.13/0.65  fof(f86,plain,(
% 2.13/0.65    m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl3_2 | ~spl3_4)),
% 2.13/0.65    inference(backward_demodulation,[],[f79,f81])).
% 2.13/0.65  fof(f79,plain,(
% 2.13/0.65    m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_4),
% 2.13/0.65    inference(avatar_component_clause,[],[f77])).
% 2.13/0.65  fof(f753,plain,(
% 2.13/0.65    spl3_14 | ~spl3_3),
% 2.13/0.65    inference(avatar_split_clause,[],[f85,f70,f750])).
% 2.13/0.65  fof(f85,plain,(
% 2.13/0.65    m1_subset_1(k4_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_3),
% 2.13/0.65    inference(backward_demodulation,[],[f75,f82])).
% 2.13/0.65  fof(f75,plain,(
% 2.13/0.65    m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_3),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f72,f45])).
% 2.13/0.65  fof(f45,plain,(
% 2.13/0.65    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.13/0.65    inference(cnf_transformation,[],[f22])).
% 2.13/0.65  fof(f22,plain,(
% 2.13/0.65    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.65    inference(ennf_transformation,[],[f8])).
% 2.13/0.65  fof(f8,axiom,(
% 2.13/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.13/0.65  fof(f433,plain,(
% 2.13/0.65    spl3_13 | ~spl3_2),
% 2.13/0.65    inference(avatar_split_clause,[],[f152,f65,f430])).
% 2.13/0.65  fof(f152,plain,(
% 2.13/0.65    m1_subset_1(k2_xboole_0(sK2,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_2),
% 2.13/0.65    inference(backward_demodulation,[],[f138,f143])).
% 2.13/0.65  fof(f138,plain,(
% 2.13/0.65    m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_2),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f67,f67,f56])).
% 2.13/0.65  fof(f428,plain,(
% 2.13/0.65    spl3_12 | ~spl3_2 | ~spl3_3),
% 2.13/0.65    inference(avatar_split_clause,[],[f151,f70,f65,f425])).
% 2.13/0.65  fof(f151,plain,(
% 2.13/0.65    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl3_2 | ~spl3_3)),
% 2.13/0.65    inference(backward_demodulation,[],[f139,f144])).
% 2.13/0.65  fof(f139,plain,(
% 2.13/0.65    m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl3_2 | ~spl3_3)),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f72,f67,f56])).
% 2.13/0.65  fof(f423,plain,(
% 2.13/0.65    spl3_11 | ~spl3_3),
% 2.13/0.65    inference(avatar_split_clause,[],[f149,f70,f420])).
% 2.13/0.65  fof(f149,plain,(
% 2.13/0.65    m1_subset_1(k2_xboole_0(sK1,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_3),
% 2.13/0.65    inference(backward_demodulation,[],[f141,f146])).
% 2.13/0.65  fof(f141,plain,(
% 2.13/0.65    m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_3),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f72,f72,f56])).
% 2.13/0.65  fof(f274,plain,(
% 2.13/0.65    spl3_10 | ~spl3_2 | ~spl3_3),
% 2.13/0.65    inference(avatar_split_clause,[],[f192,f70,f65,f271])).
% 2.13/0.65  fof(f269,plain,(
% 2.13/0.65    spl3_9 | ~spl3_3),
% 2.13/0.65    inference(avatar_split_clause,[],[f97,f70,f266])).
% 2.13/0.65  fof(f266,plain,(
% 2.13/0.65    spl3_9 <=> k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.13/0.65  fof(f97,plain,(
% 2.13/0.65    k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) | ~spl3_3),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f72,f49])).
% 2.13/0.65  fof(f264,plain,(
% 2.13/0.65    spl3_8 | ~spl3_2),
% 2.13/0.65    inference(avatar_split_clause,[],[f96,f65,f261])).
% 2.13/0.65  fof(f261,plain,(
% 2.13/0.65    spl3_8 <=> k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 2.13/0.65  fof(f96,plain,(
% 2.13/0.65    k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2) | ~spl3_2),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f67,f49])).
% 2.13/0.65  fof(f133,plain,(
% 2.13/0.65    spl3_7 | ~spl3_2),
% 2.13/0.65    inference(avatar_split_clause,[],[f106,f65,f130])).
% 2.13/0.65  fof(f106,plain,(
% 2.13/0.65    m1_subset_1(k3_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 2.13/0.65    inference(forward_demodulation,[],[f100,f96])).
% 2.13/0.65  fof(f100,plain,(
% 2.13/0.65    m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f67,f50])).
% 2.13/0.65  fof(f50,plain,(
% 2.13/0.65    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.13/0.65    inference(cnf_transformation,[],[f27])).
% 2.13/0.65  fof(f27,plain,(
% 2.13/0.65    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.13/0.65    inference(ennf_transformation,[],[f16])).
% 2.13/0.65  fof(f16,axiom,(
% 2.13/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).
% 2.13/0.65  fof(f128,plain,(
% 2.13/0.65    ~spl3_6 | ~spl3_2 | ~spl3_3),
% 2.13/0.65    inference(avatar_split_clause,[],[f121,f70,f65,f125])).
% 2.13/0.65  fof(f121,plain,(
% 2.13/0.65    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | (~spl3_2 | ~spl3_3)),
% 2.13/0.65    inference(backward_demodulation,[],[f99,f118])).
% 2.13/0.65  fof(f99,plain,(
% 2.13/0.65    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) | (~spl3_2 | ~spl3_3)),
% 2.13/0.65    inference(backward_demodulation,[],[f98,f96])).
% 2.13/0.65  fof(f98,plain,(
% 2.13/0.65    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) | ~spl3_3),
% 2.13/0.65    inference(backward_demodulation,[],[f39,f97])).
% 2.13/0.65  fof(f39,plain,(
% 2.13/0.65    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 2.13/0.65    inference(cnf_transformation,[],[f20])).
% 2.13/0.65  fof(f20,plain,(
% 2.13/0.65    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0))),
% 2.13/0.65    inference(ennf_transformation,[],[f19])).
% 2.13/0.65  fof(f19,negated_conjecture,(
% 2.13/0.65    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 2.13/0.65    inference(negated_conjecture,[],[f18])).
% 2.13/0.65  fof(f18,conjecture,(
% 2.13/0.65    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 2.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).
% 2.13/0.65  fof(f111,plain,(
% 2.13/0.65    spl3_5 | ~spl3_3),
% 2.13/0.65    inference(avatar_split_clause,[],[f105,f70,f108])).
% 2.13/0.65  fof(f105,plain,(
% 2.13/0.65    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 2.13/0.65    inference(forward_demodulation,[],[f101,f97])).
% 2.13/0.65  fof(f101,plain,(
% 2.13/0.65    m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f72,f50])).
% 2.13/0.65  fof(f80,plain,(
% 2.13/0.65    spl3_4 | ~spl3_2),
% 2.13/0.65    inference(avatar_split_clause,[],[f74,f65,f77])).
% 2.13/0.65  fof(f74,plain,(
% 2.13/0.65    m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_2),
% 2.13/0.65    inference(unit_resulting_resolution,[],[f67,f45])).
% 2.13/0.65  fof(f73,plain,(
% 2.13/0.65    spl3_3),
% 2.13/0.65    inference(avatar_split_clause,[],[f40,f70])).
% 2.13/0.65  fof(f40,plain,(
% 2.13/0.65    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.13/0.65    inference(cnf_transformation,[],[f20])).
% 2.13/0.65  fof(f68,plain,(
% 2.13/0.65    spl3_2),
% 2.13/0.65    inference(avatar_split_clause,[],[f38,f65])).
% 2.13/0.65  fof(f38,plain,(
% 2.13/0.65    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.13/0.65    inference(cnf_transformation,[],[f20])).
% 2.13/0.65  fof(f63,plain,(
% 2.13/0.65    spl3_1),
% 2.13/0.65    inference(avatar_split_clause,[],[f41,f60])).
% 2.13/0.65  fof(f60,plain,(
% 2.13/0.65    spl3_1 <=> l1_struct_0(sK0)),
% 2.13/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.13/0.65  fof(f41,plain,(
% 2.13/0.65    l1_struct_0(sK0)),
% 2.13/0.65    inference(cnf_transformation,[],[f20])).
% 2.13/0.65  % SZS output end Proof for theBenchmark
% 2.13/0.65  % (9614)------------------------------
% 2.13/0.65  % (9614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.65  % (9614)Termination reason: Refutation
% 2.13/0.65  
% 2.13/0.65  % (9614)Memory used [KB]: 2558
% 2.13/0.65  % (9614)Time elapsed: 0.167 s
% 2.13/0.65  % (9614)------------------------------
% 2.13/0.65  % (9614)------------------------------
% 2.13/0.65  % (9596)Success in time 0.292 s
%------------------------------------------------------------------------------
