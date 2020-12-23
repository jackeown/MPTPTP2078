%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 200 expanded)
%              Number of leaves         :   35 (  88 expanded)
%              Depth                    :    9
%              Number of atoms          :  321 ( 512 expanded)
%              Number of equality atoms :  104 ( 173 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1101,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f66,f68,f73,f82,f86,f90,f94,f98,f103,f115,f119,f127,f135,f140,f176,f200,f210,f220,f225,f259,f261,f378,f1095,f1100])).

fof(f1100,plain,
    ( spl2_26
    | ~ spl2_30
    | ~ spl2_71 ),
    inference(avatar_contradiction_clause,[],[f1099])).

fof(f1099,plain,
    ( $false
    | spl2_26
    | ~ spl2_30
    | ~ spl2_71 ),
    inference(subsumption_resolution,[],[f198,f1097])).

fof(f1097,plain,
    ( k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_30
    | ~ spl2_71 ),
    inference(superposition,[],[f1094,f224])).

fof(f224,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl2_30
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f1094,plain,
    ( k1_relat_1(sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_relat_1(sK1),sK0))
    | ~ spl2_71 ),
    inference(avatar_component_clause,[],[f1092])).

fof(f1092,plain,
    ( spl2_71
  <=> k1_relat_1(sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).

fof(f198,plain,
    ( k1_relat_1(sK1) != k4_xboole_0(k1_relat_1(sK1),sK0)
    | spl2_26 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl2_26
  <=> k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f1095,plain,
    ( spl2_71
    | ~ spl2_19
    | ~ spl2_41 ),
    inference(avatar_split_clause,[],[f385,f375,f138,f1092])).

fof(f138,plain,
    ( spl2_19
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f375,plain,
    ( spl2_41
  <=> k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f385,plain,
    ( k1_relat_1(sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_relat_1(sK1),sK0))
    | ~ spl2_19
    | ~ spl2_41 ),
    inference(superposition,[],[f139,f377])).

fof(f377,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f375])).

fof(f139,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f138])).

fof(f378,plain,
    ( spl2_41
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f269,f208,f70,f59,f375])).

fof(f59,plain,
    ( spl2_2
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f70,plain,
    ( spl2_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f208,plain,
    ( spl2_27
  <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f269,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_27 ),
    inference(forward_demodulation,[],[f264,f72])).

fof(f72,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f264,plain,
    ( k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_2
    | ~ spl2_27 ),
    inference(superposition,[],[f209,f61])).

fof(f61,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f209,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f208])).

fof(f261,plain,
    ( spl2_3
    | ~ spl2_15
    | ~ spl2_26 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | spl2_3
    | ~ spl2_15
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f205,f64])).

fof(f64,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_3
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f205,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_15
    | ~ spl2_26 ),
    inference(trivial_inequality_removal,[],[f204])).

fof(f204,plain,
    ( k1_relat_1(sK1) != k1_relat_1(sK1)
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_15
    | ~ spl2_26 ),
    inference(superposition,[],[f118,f199])).

fof(f199,plain,
    ( k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f197])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != X0
        | r1_xboole_0(X0,X1) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f259,plain,
    ( ~ spl2_6
    | ~ spl2_8
    | ~ spl2_18
    | ~ spl2_26
    | ~ spl2_27
    | spl2_29 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_18
    | ~ spl2_26
    | ~ spl2_27
    | spl2_29 ),
    inference(subsumption_resolution,[],[f206,f256])).

fof(f256,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_27
    | spl2_29 ),
    inference(superposition,[],[f219,f209])).

fof(f219,plain,
    ( k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_29 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl2_29
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f206,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_18
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f203,f164])).

fof(f164,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f158,f81])).

fof(f81,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl2_6
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f158,plain,
    ( ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(superposition,[],[f134,f89])).

fof(f89,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl2_8
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f134,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl2_18
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f203,plain,
    ( k3_xboole_0(k1_relat_1(sK1),sK0) = k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ spl2_18
    | ~ spl2_26 ),
    inference(superposition,[],[f134,f199])).

fof(f225,plain,
    ( spl2_30
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f120,f96,f84,f223])).

fof(f84,plain,
    ( spl2_7
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f96,plain,
    ( spl2_10
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f120,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(superposition,[],[f97,f85])).

fof(f85,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f97,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f220,plain,
    ( ~ spl2_29
    | spl2_2
    | ~ spl2_11
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f150,f125,f101,f59,f217])).

fof(f101,plain,
    ( spl2_11
  <=> ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f125,plain,
    ( spl2_16
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 != k1_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f150,plain,
    ( k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_2
    | ~ spl2_11
    | ~ spl2_16 ),
    inference(unit_resulting_resolution,[],[f102,f60,f126])).

fof(f126,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(X0)
        | k1_xboole_0 = X0
        | ~ v1_relat_1(X0) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f125])).

fof(f60,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f102,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f101])).

fof(f210,plain,
    ( spl2_27
    | ~ spl2_1
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f181,f174,f54,f208])).

fof(f54,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f174,plain,
    ( spl2_22
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f181,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)
    | ~ spl2_1
    | ~ spl2_22 ),
    inference(unit_resulting_resolution,[],[f56,f175])).

fof(f175,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f174])).

fof(f56,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f200,plain,
    ( spl2_26
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f141,f113,f63,f197])).

fof(f113,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f141,plain,
    ( k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f65,f114])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f113])).

fof(f65,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f176,plain,(
    spl2_22 ),
    inference(avatar_split_clause,[],[f46,f174])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f140,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f44,f138])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f135,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f43,f133])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f127,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f38,f125])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f119,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f48,f117])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f115,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f47,f113])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f103,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f99,f92,f54,f101])).

fof(f92,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f99,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f56,f93])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f98,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f40,f96])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f94,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f45,f92])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f90,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f37,f88])).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f86,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f36,f84])).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f82,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f35,f80])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f73,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f33,f70])).

fof(f33,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f68,plain,
    ( ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f67,f63,f59])).

fof(f67,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f32,f65])).

fof(f32,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k7_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k7_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k7_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f66,plain,
    ( spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f31,f63,f59])).

fof(f31,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f30,f54])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:33:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.43  % (20891)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.45  % (20891)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f1101,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f57,f66,f68,f73,f82,f86,f90,f94,f98,f103,f115,f119,f127,f135,f140,f176,f200,f210,f220,f225,f259,f261,f378,f1095,f1100])).
% 0.22/0.45  fof(f1100,plain,(
% 0.22/0.45    spl2_26 | ~spl2_30 | ~spl2_71),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f1099])).
% 0.22/0.45  fof(f1099,plain,(
% 0.22/0.45    $false | (spl2_26 | ~spl2_30 | ~spl2_71)),
% 0.22/0.45    inference(subsumption_resolution,[],[f198,f1097])).
% 0.22/0.45  fof(f1097,plain,(
% 0.22/0.45    k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),sK0) | (~spl2_30 | ~spl2_71)),
% 0.22/0.45    inference(superposition,[],[f1094,f224])).
% 0.22/0.45  fof(f224,plain,(
% 0.22/0.45    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl2_30),
% 0.22/0.45    inference(avatar_component_clause,[],[f223])).
% 0.22/0.45  fof(f223,plain,(
% 0.22/0.45    spl2_30 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.22/0.45  fof(f1094,plain,(
% 0.22/0.45    k1_relat_1(sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_relat_1(sK1),sK0)) | ~spl2_71),
% 0.22/0.45    inference(avatar_component_clause,[],[f1092])).
% 0.22/0.45  fof(f1092,plain,(
% 0.22/0.45    spl2_71 <=> k1_relat_1(sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_relat_1(sK1),sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).
% 0.22/0.45  fof(f198,plain,(
% 0.22/0.45    k1_relat_1(sK1) != k4_xboole_0(k1_relat_1(sK1),sK0) | spl2_26),
% 0.22/0.45    inference(avatar_component_clause,[],[f197])).
% 0.22/0.45  fof(f197,plain,(
% 0.22/0.45    spl2_26 <=> k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.22/0.45  fof(f1095,plain,(
% 0.22/0.45    spl2_71 | ~spl2_19 | ~spl2_41),
% 0.22/0.45    inference(avatar_split_clause,[],[f385,f375,f138,f1092])).
% 0.22/0.45  fof(f138,plain,(
% 0.22/0.45    spl2_19 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.45  fof(f375,plain,(
% 0.22/0.45    spl2_41 <=> k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 0.22/0.45  fof(f385,plain,(
% 0.22/0.45    k1_relat_1(sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_relat_1(sK1),sK0)) | (~spl2_19 | ~spl2_41)),
% 0.22/0.45    inference(superposition,[],[f139,f377])).
% 0.22/0.45  fof(f377,plain,(
% 0.22/0.45    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_41),
% 0.22/0.45    inference(avatar_component_clause,[],[f375])).
% 0.22/0.45  fof(f139,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | ~spl2_19),
% 0.22/0.45    inference(avatar_component_clause,[],[f138])).
% 0.22/0.45  fof(f378,plain,(
% 0.22/0.45    spl2_41 | ~spl2_2 | ~spl2_4 | ~spl2_27),
% 0.22/0.45    inference(avatar_split_clause,[],[f269,f208,f70,f59,f375])).
% 0.22/0.45  fof(f59,plain,(
% 0.22/0.45    spl2_2 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.45  fof(f70,plain,(
% 0.22/0.45    spl2_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.45  fof(f208,plain,(
% 0.22/0.45    spl2_27 <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.22/0.46  fof(f269,plain,(
% 0.22/0.46    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0) | (~spl2_2 | ~spl2_4 | ~spl2_27)),
% 0.22/0.46    inference(forward_demodulation,[],[f264,f72])).
% 0.22/0.46  fof(f72,plain,(
% 0.22/0.46    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl2_4),
% 0.22/0.46    inference(avatar_component_clause,[],[f70])).
% 0.22/0.46  fof(f264,plain,(
% 0.22/0.46    k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_relat_1(sK1),sK0) | (~spl2_2 | ~spl2_27)),
% 0.22/0.46    inference(superposition,[],[f209,f61])).
% 0.22/0.46  fof(f61,plain,(
% 0.22/0.46    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl2_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f59])).
% 0.22/0.46  fof(f209,plain,(
% 0.22/0.46    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)) ) | ~spl2_27),
% 0.22/0.46    inference(avatar_component_clause,[],[f208])).
% 0.22/0.46  fof(f261,plain,(
% 0.22/0.46    spl2_3 | ~spl2_15 | ~spl2_26),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f260])).
% 0.22/0.46  fof(f260,plain,(
% 0.22/0.46    $false | (spl2_3 | ~spl2_15 | ~spl2_26)),
% 0.22/0.46    inference(subsumption_resolution,[],[f205,f64])).
% 0.22/0.46  fof(f64,plain,(
% 0.22/0.46    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl2_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f63])).
% 0.22/0.46  fof(f63,plain,(
% 0.22/0.46    spl2_3 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.46  fof(f205,plain,(
% 0.22/0.46    r1_xboole_0(k1_relat_1(sK1),sK0) | (~spl2_15 | ~spl2_26)),
% 0.22/0.46    inference(trivial_inequality_removal,[],[f204])).
% 0.22/0.46  fof(f204,plain,(
% 0.22/0.46    k1_relat_1(sK1) != k1_relat_1(sK1) | r1_xboole_0(k1_relat_1(sK1),sK0) | (~spl2_15 | ~spl2_26)),
% 0.22/0.46    inference(superposition,[],[f118,f199])).
% 0.22/0.46  fof(f199,plain,(
% 0.22/0.46    k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_26),
% 0.22/0.46    inference(avatar_component_clause,[],[f197])).
% 0.22/0.46  fof(f118,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) ) | ~spl2_15),
% 0.22/0.46    inference(avatar_component_clause,[],[f117])).
% 0.22/0.46  fof(f117,plain,(
% 0.22/0.46    spl2_15 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.46  fof(f259,plain,(
% 0.22/0.46    ~spl2_6 | ~spl2_8 | ~spl2_18 | ~spl2_26 | ~spl2_27 | spl2_29),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f258])).
% 0.22/0.46  fof(f258,plain,(
% 0.22/0.46    $false | (~spl2_6 | ~spl2_8 | ~spl2_18 | ~spl2_26 | ~spl2_27 | spl2_29)),
% 0.22/0.46    inference(subsumption_resolution,[],[f206,f256])).
% 0.22/0.46  fof(f256,plain,(
% 0.22/0.46    k1_xboole_0 != k3_xboole_0(k1_relat_1(sK1),sK0) | (~spl2_27 | spl2_29)),
% 0.22/0.46    inference(superposition,[],[f219,f209])).
% 0.22/0.46  fof(f219,plain,(
% 0.22/0.46    k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,sK0)) | spl2_29),
% 0.22/0.46    inference(avatar_component_clause,[],[f217])).
% 0.22/0.46  fof(f217,plain,(
% 0.22/0.46    spl2_29 <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.22/0.46  fof(f206,plain,(
% 0.22/0.46    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0) | (~spl2_6 | ~spl2_8 | ~spl2_18 | ~spl2_26)),
% 0.22/0.46    inference(forward_demodulation,[],[f203,f164])).
% 0.22/0.46  fof(f164,plain,(
% 0.22/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl2_6 | ~spl2_8 | ~spl2_18)),
% 0.22/0.46    inference(forward_demodulation,[],[f158,f81])).
% 0.22/0.46  fof(f81,plain,(
% 0.22/0.46    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl2_6),
% 0.22/0.46    inference(avatar_component_clause,[],[f80])).
% 0.22/0.46  fof(f80,plain,(
% 0.22/0.46    spl2_6 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.46  fof(f158,plain,(
% 0.22/0.46    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) ) | (~spl2_8 | ~spl2_18)),
% 0.22/0.46    inference(superposition,[],[f134,f89])).
% 0.22/0.46  fof(f89,plain,(
% 0.22/0.46    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_8),
% 0.22/0.46    inference(avatar_component_clause,[],[f88])).
% 0.22/0.46  fof(f88,plain,(
% 0.22/0.46    spl2_8 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.46  fof(f134,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) ) | ~spl2_18),
% 0.22/0.46    inference(avatar_component_clause,[],[f133])).
% 0.22/0.46  fof(f133,plain,(
% 0.22/0.46    spl2_18 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.46  fof(f203,plain,(
% 0.22/0.46    k3_xboole_0(k1_relat_1(sK1),sK0) = k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)) | (~spl2_18 | ~spl2_26)),
% 0.22/0.46    inference(superposition,[],[f134,f199])).
% 0.22/0.46  fof(f225,plain,(
% 0.22/0.46    spl2_30 | ~spl2_7 | ~spl2_10),
% 0.22/0.46    inference(avatar_split_clause,[],[f120,f96,f84,f223])).
% 0.22/0.46  fof(f84,plain,(
% 0.22/0.46    spl2_7 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.46  fof(f96,plain,(
% 0.22/0.46    spl2_10 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.46  fof(f120,plain,(
% 0.22/0.46    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl2_7 | ~spl2_10)),
% 0.22/0.46    inference(superposition,[],[f97,f85])).
% 0.22/0.46  fof(f85,plain,(
% 0.22/0.46    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_7),
% 0.22/0.46    inference(avatar_component_clause,[],[f84])).
% 0.22/0.46  fof(f97,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_10),
% 0.22/0.46    inference(avatar_component_clause,[],[f96])).
% 0.22/0.46  fof(f220,plain,(
% 0.22/0.46    ~spl2_29 | spl2_2 | ~spl2_11 | ~spl2_16),
% 0.22/0.46    inference(avatar_split_clause,[],[f150,f125,f101,f59,f217])).
% 0.22/0.46  fof(f101,plain,(
% 0.22/0.46    spl2_11 <=> ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.46  fof(f125,plain,(
% 0.22/0.46    spl2_16 <=> ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.46  fof(f150,plain,(
% 0.22/0.46    k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,sK0)) | (spl2_2 | ~spl2_11 | ~spl2_16)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f102,f60,f126])).
% 0.22/0.46  fof(f126,plain,(
% 0.22/0.46    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) ) | ~spl2_16),
% 0.22/0.46    inference(avatar_component_clause,[],[f125])).
% 0.22/0.46  fof(f60,plain,(
% 0.22/0.46    k1_xboole_0 != k7_relat_1(sK1,sK0) | spl2_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f59])).
% 0.22/0.46  fof(f102,plain,(
% 0.22/0.46    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl2_11),
% 0.22/0.46    inference(avatar_component_clause,[],[f101])).
% 0.22/0.46  fof(f210,plain,(
% 0.22/0.46    spl2_27 | ~spl2_1 | ~spl2_22),
% 0.22/0.46    inference(avatar_split_clause,[],[f181,f174,f54,f208])).
% 0.22/0.46  fof(f54,plain,(
% 0.22/0.46    spl2_1 <=> v1_relat_1(sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.46  fof(f174,plain,(
% 0.22/0.46    spl2_22 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.22/0.46  fof(f181,plain,(
% 0.22/0.46    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)) ) | (~spl2_1 | ~spl2_22)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f56,f175])).
% 0.22/0.46  fof(f175,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl2_22),
% 0.22/0.46    inference(avatar_component_clause,[],[f174])).
% 0.22/0.46  fof(f56,plain,(
% 0.22/0.46    v1_relat_1(sK1) | ~spl2_1),
% 0.22/0.46    inference(avatar_component_clause,[],[f54])).
% 0.22/0.46  fof(f200,plain,(
% 0.22/0.46    spl2_26 | ~spl2_3 | ~spl2_14),
% 0.22/0.46    inference(avatar_split_clause,[],[f141,f113,f63,f197])).
% 0.22/0.46  fof(f113,plain,(
% 0.22/0.46    spl2_14 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.46  fof(f141,plain,(
% 0.22/0.46    k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),sK0) | (~spl2_3 | ~spl2_14)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f65,f114])).
% 0.22/0.46  fof(f114,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) ) | ~spl2_14),
% 0.22/0.46    inference(avatar_component_clause,[],[f113])).
% 0.22/0.46  fof(f65,plain,(
% 0.22/0.46    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f63])).
% 0.22/0.46  fof(f176,plain,(
% 0.22/0.46    spl2_22),
% 0.22/0.46    inference(avatar_split_clause,[],[f46,f174])).
% 0.22/0.46  fof(f46,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f24])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f17])).
% 0.22/0.46  fof(f17,axiom,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.22/0.46  fof(f140,plain,(
% 0.22/0.46    spl2_19),
% 0.22/0.46    inference(avatar_split_clause,[],[f44,f138])).
% 0.22/0.46  fof(f44,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.46  fof(f135,plain,(
% 0.22/0.46    spl2_18),
% 0.22/0.46    inference(avatar_split_clause,[],[f43,f133])).
% 0.22/0.46  fof(f43,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.46  fof(f127,plain,(
% 0.22/0.46    spl2_16),
% 0.22/0.46    inference(avatar_split_clause,[],[f38,f125])).
% 0.22/0.46  fof(f38,plain,(
% 0.22/0.46    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f22])).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(flattening,[],[f21])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f16])).
% 0.22/0.46  fof(f16,axiom,(
% 0.22/0.46    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.46  fof(f119,plain,(
% 0.22/0.46    spl2_15),
% 0.22/0.46    inference(avatar_split_clause,[],[f48,f117])).
% 0.22/0.46  fof(f48,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f29])).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.46    inference(nnf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,axiom,(
% 0.22/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.46  fof(f115,plain,(
% 0.22/0.46    spl2_14),
% 0.22/0.46    inference(avatar_split_clause,[],[f47,f113])).
% 0.22/0.46  fof(f47,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f29])).
% 0.22/0.46  fof(f103,plain,(
% 0.22/0.46    spl2_11 | ~spl2_1 | ~spl2_9),
% 0.22/0.46    inference(avatar_split_clause,[],[f99,f92,f54,f101])).
% 0.22/0.46  fof(f92,plain,(
% 0.22/0.46    spl2_9 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.46  fof(f99,plain,(
% 0.22/0.46    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | (~spl2_1 | ~spl2_9)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f56,f93])).
% 0.22/0.46  fof(f93,plain,(
% 0.22/0.46    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl2_9),
% 0.22/0.46    inference(avatar_component_clause,[],[f92])).
% 0.22/0.46  fof(f98,plain,(
% 0.22/0.46    spl2_10),
% 0.22/0.46    inference(avatar_split_clause,[],[f40,f96])).
% 0.22/0.46  fof(f40,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.46  fof(f94,plain,(
% 0.22/0.46    spl2_9),
% 0.22/0.46    inference(avatar_split_clause,[],[f45,f92])).
% 0.22/0.46  fof(f45,plain,(
% 0.22/0.46    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f23])).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f14])).
% 0.22/0.46  fof(f14,axiom,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.46  fof(f90,plain,(
% 0.22/0.46    spl2_8),
% 0.22/0.46    inference(avatar_split_clause,[],[f37,f88])).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.46  fof(f86,plain,(
% 0.22/0.46    spl2_7),
% 0.22/0.46    inference(avatar_split_clause,[],[f36,f84])).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.46  fof(f82,plain,(
% 0.22/0.46    spl2_6),
% 0.22/0.46    inference(avatar_split_clause,[],[f35,f80])).
% 0.22/0.46  fof(f35,plain,(
% 0.22/0.46    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.46  fof(f73,plain,(
% 0.22/0.46    spl2_4),
% 0.22/0.46    inference(avatar_split_clause,[],[f33,f70])).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.46    inference(cnf_transformation,[],[f15])).
% 0.22/0.46  fof(f15,axiom,(
% 0.22/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.46  fof(f68,plain,(
% 0.22/0.46    ~spl2_2 | ~spl2_3),
% 0.22/0.46    inference(avatar_split_clause,[],[f67,f63,f59])).
% 0.22/0.46  fof(f67,plain,(
% 0.22/0.46    k1_xboole_0 != k7_relat_1(sK1,sK0) | ~spl2_3),
% 0.22/0.46    inference(subsumption_resolution,[],[f32,f65])).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f28])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.22/0.46    inference(flattening,[],[f25])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.22/0.46    inference(nnf_transformation,[],[f20])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f19])).
% 0.22/0.46  fof(f19,negated_conjecture,(
% 0.22/0.46    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.46    inference(negated_conjecture,[],[f18])).
% 0.22/0.46  fof(f18,conjecture,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.22/0.46  fof(f66,plain,(
% 0.22/0.46    spl2_2 | spl2_3),
% 0.22/0.46    inference(avatar_split_clause,[],[f31,f63,f59])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f28])).
% 0.22/0.46  fof(f57,plain,(
% 0.22/0.46    spl2_1),
% 0.22/0.46    inference(avatar_split_clause,[],[f30,f54])).
% 0.22/0.46  fof(f30,plain,(
% 0.22/0.46    v1_relat_1(sK1)),
% 0.22/0.46    inference(cnf_transformation,[],[f28])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (20891)------------------------------
% 0.22/0.46  % (20891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (20891)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (20891)Memory used [KB]: 6780
% 0.22/0.46  % (20891)Time elapsed: 0.030 s
% 0.22/0.46  % (20891)------------------------------
% 0.22/0.46  % (20891)------------------------------
% 0.22/0.46  % (20885)Success in time 0.099 s
%------------------------------------------------------------------------------
