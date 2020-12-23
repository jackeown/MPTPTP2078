%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 190 expanded)
%              Number of leaves         :   29 (  90 expanded)
%              Depth                    :    8
%              Number of atoms          :  300 ( 561 expanded)
%              Number of equality atoms :   25 (  45 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f515,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f56,f64,f68,f75,f79,f90,f94,f116,f124,f132,f139,f145,f205,f212,f328,f459,f496])).

fof(f496,plain,
    ( spl2_4
    | ~ spl2_10
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_27
    | ~ spl2_39
    | ~ spl2_47 ),
    inference(avatar_contradiction_clause,[],[f495])).

fof(f495,plain,
    ( $false
    | spl2_4
    | ~ spl2_10
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_27
    | ~ spl2_39
    | ~ spl2_47 ),
    inference(subsumption_resolution,[],[f51,f494])).

fof(f494,plain,
    ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | ~ spl2_10
    | ~ spl2_17
    | ~ spl2_18
    | ~ spl2_27
    | ~ spl2_39
    | ~ spl2_47 ),
    inference(forward_demodulation,[],[f493,f131])).

fof(f131,plain,
    ( k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl2_17
  <=> k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f493,plain,
    ( r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(sK1))
    | ~ spl2_10
    | ~ spl2_18
    | ~ spl2_27
    | ~ spl2_39
    | ~ spl2_47 ),
    inference(forward_demodulation,[],[f492,f327])).

fof(f327,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl2_39
  <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f492,plain,
    ( r1_tarski(k2_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0)),k3_relat_1(sK1))
    | ~ spl2_10
    | ~ spl2_18
    | ~ spl2_27
    | ~ spl2_47 ),
    inference(forward_demodulation,[],[f479,f138])).

fof(f138,plain,
    ( k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl2_18
  <=> k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f479,plain,
    ( r1_tarski(k2_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0)),k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)))
    | ~ spl2_10
    | ~ spl2_27
    | ~ spl2_47 ),
    inference(unit_resulting_resolution,[],[f211,f458,f78])).

fof(f78,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k2_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl2_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f458,plain,
    ( ! [X8] : r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),X8))
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f457])).

fof(f457,plain,
    ( spl2_47
  <=> ! [X8] : r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f211,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(sK0),k2_xboole_0(X0,k2_relat_1(sK1)))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl2_27
  <=> ! [X0] : r1_tarski(k2_relat_1(sK0),k2_xboole_0(X0,k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f51,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl2_4
  <=> r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f459,plain,
    ( spl2_47
    | ~ spl2_26
    | ~ spl2_39 ),
    inference(avatar_split_clause,[],[f332,f326,f203,f457])).

fof(f203,plain,
    ( spl2_26
  <=> ! [X0] : r1_tarski(k1_relat_1(sK0),k2_xboole_0(X0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f332,plain,
    ( ! [X8] : r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),X8))
    | ~ spl2_26
    | ~ spl2_39 ),
    inference(superposition,[],[f204,f327])).

fof(f204,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(sK0),k2_xboole_0(X0,k1_relat_1(sK1)))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f203])).

fof(f328,plain,
    ( spl2_39
    | ~ spl2_7
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f152,f143,f62,f326])).

fof(f62,plain,
    ( spl2_7
  <=> ! [X1,X0] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f143,plain,
    ( spl2_19
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f152,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)
    | ~ spl2_7
    | ~ spl2_19 ),
    inference(superposition,[],[f144,f63])).

fof(f63,plain,
    ( ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f144,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f143])).

fof(f212,plain,
    ( spl2_27
    | ~ spl2_8
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f127,f121,f66,f210])).

fof(f66,plain,
    ( spl2_8
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k2_xboole_0(X2,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f121,plain,
    ( spl2_16
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f127,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(sK0),k2_xboole_0(X0,k2_relat_1(sK1)))
    | ~ spl2_8
    | ~ spl2_16 ),
    inference(unit_resulting_resolution,[],[f123,f67])).

fof(f67,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k2_xboole_0(X2,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f123,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f121])).

fof(f205,plain,
    ( spl2_26
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f119,f113,f66,f203])).

fof(f113,plain,
    ( spl2_15
  <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f119,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(sK0),k2_xboole_0(X0,k1_relat_1(sK1)))
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(unit_resulting_resolution,[],[f115,f67])).

fof(f115,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f113])).

fof(f145,plain,
    ( spl2_19
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f69,f62,f54,f143])).

fof(f54,plain,
    ( spl2_5
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f69,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(superposition,[],[f63,f55])).

fof(f55,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f139,plain,
    ( spl2_18
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f81,f73,f39,f136])).

fof(f39,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f73,plain,
    ( spl2_9
  <=> ! [X0] :
        ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f81,plain,
    ( k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f41,f74])).

fof(f74,plain,
    ( ! [X0] :
        ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f73])).

fof(f41,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f132,plain,
    ( spl2_17
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f80,f73,f34,f129])).

fof(f34,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f80,plain,
    ( k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f36,f74])).

fof(f36,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f124,plain,
    ( spl2_16
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f98,f92,f44,f39,f34,f121])).

fof(f44,plain,
    ( spl2_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f92,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f98,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_13 ),
    inference(unit_resulting_resolution,[],[f36,f41,f46,f93])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f92])).

fof(f46,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f116,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f97,f88,f44,f39,f34,f113])).

fof(f88,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f97,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f36,f41,f46,f89])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f88])).

fof(f94,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f27,f92])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f90,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f26,f88])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f79,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f32,f77])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f75,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f25,f73])).

fof(f25,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f68,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f31,f66])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f64,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f30,f62])).

fof(f30,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f56,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f28,f54])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f52,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f47,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f23,f44])).

fof(f23,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f22,f39])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f21,f34])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:25:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (23300)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.45  % (23300)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f515,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f56,f64,f68,f75,f79,f90,f94,f116,f124,f132,f139,f145,f205,f212,f328,f459,f496])).
% 0.22/0.45  fof(f496,plain,(
% 0.22/0.45    spl2_4 | ~spl2_10 | ~spl2_17 | ~spl2_18 | ~spl2_27 | ~spl2_39 | ~spl2_47),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f495])).
% 0.22/0.45  fof(f495,plain,(
% 0.22/0.45    $false | (spl2_4 | ~spl2_10 | ~spl2_17 | ~spl2_18 | ~spl2_27 | ~spl2_39 | ~spl2_47)),
% 0.22/0.45    inference(subsumption_resolution,[],[f51,f494])).
% 0.22/0.45  fof(f494,plain,(
% 0.22/0.45    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) | (~spl2_10 | ~spl2_17 | ~spl2_18 | ~spl2_27 | ~spl2_39 | ~spl2_47)),
% 0.22/0.45    inference(forward_demodulation,[],[f493,f131])).
% 0.22/0.45  fof(f131,plain,(
% 0.22/0.45    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) | ~spl2_17),
% 0.22/0.45    inference(avatar_component_clause,[],[f129])).
% 0.22/0.45  fof(f129,plain,(
% 0.22/0.45    spl2_17 <=> k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.45  fof(f493,plain,(
% 0.22/0.45    r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(sK1)) | (~spl2_10 | ~spl2_18 | ~spl2_27 | ~spl2_39 | ~spl2_47)),
% 0.22/0.45    inference(forward_demodulation,[],[f492,f327])).
% 0.22/0.45  fof(f327,plain,(
% 0.22/0.45    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) ) | ~spl2_39),
% 0.22/0.45    inference(avatar_component_clause,[],[f326])).
% 0.22/0.45  fof(f326,plain,(
% 0.22/0.45    spl2_39 <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 0.22/0.45  fof(f492,plain,(
% 0.22/0.45    r1_tarski(k2_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0)),k3_relat_1(sK1)) | (~spl2_10 | ~spl2_18 | ~spl2_27 | ~spl2_47)),
% 0.22/0.45    inference(forward_demodulation,[],[f479,f138])).
% 0.22/0.45  fof(f138,plain,(
% 0.22/0.45    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) | ~spl2_18),
% 0.22/0.45    inference(avatar_component_clause,[],[f136])).
% 0.22/0.45  fof(f136,plain,(
% 0.22/0.45    spl2_18 <=> k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.45  fof(f479,plain,(
% 0.22/0.45    r1_tarski(k2_xboole_0(k2_relat_1(sK0),k1_relat_1(sK0)),k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))) | (~spl2_10 | ~spl2_27 | ~spl2_47)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f211,f458,f78])).
% 0.22/0.45  fof(f78,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) ) | ~spl2_10),
% 0.22/0.45    inference(avatar_component_clause,[],[f77])).
% 0.22/0.45  fof(f77,plain,(
% 0.22/0.45    spl2_10 <=> ! [X1,X0,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.45  fof(f458,plain,(
% 0.22/0.45    ( ! [X8] : (r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),X8))) ) | ~spl2_47),
% 0.22/0.45    inference(avatar_component_clause,[],[f457])).
% 0.22/0.45  fof(f457,plain,(
% 0.22/0.45    spl2_47 <=> ! [X8] : r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),X8))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 0.22/0.45  fof(f211,plain,(
% 0.22/0.45    ( ! [X0] : (r1_tarski(k2_relat_1(sK0),k2_xboole_0(X0,k2_relat_1(sK1)))) ) | ~spl2_27),
% 0.22/0.45    inference(avatar_component_clause,[],[f210])).
% 0.22/0.45  fof(f210,plain,(
% 0.22/0.45    spl2_27 <=> ! [X0] : r1_tarski(k2_relat_1(sK0),k2_xboole_0(X0,k2_relat_1(sK1)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.22/0.45  fof(f51,plain,(
% 0.22/0.45    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) | spl2_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f49])).
% 0.22/0.45  fof(f49,plain,(
% 0.22/0.45    spl2_4 <=> r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.45  fof(f459,plain,(
% 0.22/0.45    spl2_47 | ~spl2_26 | ~spl2_39),
% 0.22/0.45    inference(avatar_split_clause,[],[f332,f326,f203,f457])).
% 0.22/0.45  fof(f203,plain,(
% 0.22/0.45    spl2_26 <=> ! [X0] : r1_tarski(k1_relat_1(sK0),k2_xboole_0(X0,k1_relat_1(sK1)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.22/0.45  fof(f332,plain,(
% 0.22/0.45    ( ! [X8] : (r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),X8))) ) | (~spl2_26 | ~spl2_39)),
% 0.22/0.45    inference(superposition,[],[f204,f327])).
% 0.22/0.45  fof(f204,plain,(
% 0.22/0.45    ( ! [X0] : (r1_tarski(k1_relat_1(sK0),k2_xboole_0(X0,k1_relat_1(sK1)))) ) | ~spl2_26),
% 0.22/0.45    inference(avatar_component_clause,[],[f203])).
% 0.22/0.45  fof(f328,plain,(
% 0.22/0.45    spl2_39 | ~spl2_7 | ~spl2_19),
% 0.22/0.45    inference(avatar_split_clause,[],[f152,f143,f62,f326])).
% 0.22/0.45  fof(f62,plain,(
% 0.22/0.45    spl2_7 <=> ! [X1,X0] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.45  fof(f143,plain,(
% 0.22/0.45    spl2_19 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.45  fof(f152,plain,(
% 0.22/0.45    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) ) | (~spl2_7 | ~spl2_19)),
% 0.22/0.45    inference(superposition,[],[f144,f63])).
% 0.22/0.45  fof(f63,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) ) | ~spl2_7),
% 0.22/0.45    inference(avatar_component_clause,[],[f62])).
% 0.22/0.45  fof(f144,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) ) | ~spl2_19),
% 0.22/0.45    inference(avatar_component_clause,[],[f143])).
% 0.22/0.45  fof(f212,plain,(
% 0.22/0.45    spl2_27 | ~spl2_8 | ~spl2_16),
% 0.22/0.45    inference(avatar_split_clause,[],[f127,f121,f66,f210])).
% 0.22/0.45  fof(f66,plain,(
% 0.22/0.45    spl2_8 <=> ! [X1,X0,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.45  fof(f121,plain,(
% 0.22/0.45    spl2_16 <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.45  fof(f127,plain,(
% 0.22/0.45    ( ! [X0] : (r1_tarski(k2_relat_1(sK0),k2_xboole_0(X0,k2_relat_1(sK1)))) ) | (~spl2_8 | ~spl2_16)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f123,f67])).
% 0.22/0.45  fof(f67,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_8),
% 0.22/0.45    inference(avatar_component_clause,[],[f66])).
% 0.22/0.45  fof(f123,plain,(
% 0.22/0.45    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~spl2_16),
% 0.22/0.45    inference(avatar_component_clause,[],[f121])).
% 0.22/0.45  fof(f205,plain,(
% 0.22/0.45    spl2_26 | ~spl2_8 | ~spl2_15),
% 0.22/0.45    inference(avatar_split_clause,[],[f119,f113,f66,f203])).
% 0.22/0.45  fof(f113,plain,(
% 0.22/0.45    spl2_15 <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.45  fof(f119,plain,(
% 0.22/0.45    ( ! [X0] : (r1_tarski(k1_relat_1(sK0),k2_xboole_0(X0,k1_relat_1(sK1)))) ) | (~spl2_8 | ~spl2_15)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f115,f67])).
% 0.22/0.45  fof(f115,plain,(
% 0.22/0.45    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | ~spl2_15),
% 0.22/0.45    inference(avatar_component_clause,[],[f113])).
% 0.22/0.45  fof(f145,plain,(
% 0.22/0.45    spl2_19 | ~spl2_5 | ~spl2_7),
% 0.22/0.45    inference(avatar_split_clause,[],[f69,f62,f54,f143])).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    spl2_5 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.45  fof(f69,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) ) | (~spl2_5 | ~spl2_7)),
% 0.22/0.45    inference(superposition,[],[f63,f55])).
% 0.22/0.45  fof(f55,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl2_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f54])).
% 0.22/0.45  fof(f139,plain,(
% 0.22/0.45    spl2_18 | ~spl2_2 | ~spl2_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f81,f73,f39,f136])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    spl2_2 <=> v1_relat_1(sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.45  fof(f73,plain,(
% 0.22/0.45    spl2_9 <=> ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.45  fof(f81,plain,(
% 0.22/0.45    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) | (~spl2_2 | ~spl2_9)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f41,f74])).
% 0.22/0.45  fof(f74,plain,(
% 0.22/0.45    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl2_9),
% 0.22/0.45    inference(avatar_component_clause,[],[f73])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    v1_relat_1(sK1) | ~spl2_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f39])).
% 0.22/0.45  fof(f132,plain,(
% 0.22/0.45    spl2_17 | ~spl2_1 | ~spl2_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f80,f73,f34,f129])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    spl2_1 <=> v1_relat_1(sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.45  fof(f80,plain,(
% 0.22/0.45    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) | (~spl2_1 | ~spl2_9)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f36,f74])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    v1_relat_1(sK0) | ~spl2_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f34])).
% 0.22/0.45  fof(f124,plain,(
% 0.22/0.45    spl2_16 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_13),
% 0.22/0.45    inference(avatar_split_clause,[],[f98,f92,f44,f39,f34,f121])).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    spl2_3 <=> r1_tarski(sK0,sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.45  fof(f92,plain,(
% 0.22/0.45    spl2_13 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.45  fof(f98,plain,(
% 0.22/0.45    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_13)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f36,f41,f46,f93])).
% 0.22/0.45  fof(f93,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_13),
% 0.22/0.45    inference(avatar_component_clause,[],[f92])).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    r1_tarski(sK0,sK1) | ~spl2_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f44])).
% 0.22/0.45  fof(f116,plain,(
% 0.22/0.45    spl2_15 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_12),
% 0.22/0.45    inference(avatar_split_clause,[],[f97,f88,f44,f39,f34,f113])).
% 0.22/0.45  fof(f88,plain,(
% 0.22/0.45    spl2_12 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.45  fof(f97,plain,(
% 0.22/0.45    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_12)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f36,f41,f46,f89])).
% 0.22/0.45  fof(f89,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_12),
% 0.22/0.45    inference(avatar_component_clause,[],[f88])).
% 0.22/0.45  fof(f94,plain,(
% 0.22/0.45    spl2_13),
% 0.22/0.45    inference(avatar_split_clause,[],[f27,f92])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(flattening,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.22/0.45  fof(f90,plain,(
% 0.22/0.45    spl2_12),
% 0.22/0.45    inference(avatar_split_clause,[],[f26,f88])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f79,plain,(
% 0.22/0.45    spl2_10),
% 0.22/0.45    inference(avatar_split_clause,[],[f32,f77])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.45    inference(flattening,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.22/0.45    inference(ennf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.22/0.45  fof(f75,plain,(
% 0.22/0.45    spl2_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f25,f73])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,axiom,(
% 0.22/0.45    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.22/0.45  fof(f68,plain,(
% 0.22/0.45    spl2_8),
% 0.22/0.45    inference(avatar_split_clause,[],[f31,f66])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.22/0.45  fof(f64,plain,(
% 0.22/0.45    spl2_7),
% 0.22/0.45    inference(avatar_split_clause,[],[f30,f62])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.45  fof(f56,plain,(
% 0.22/0.45    spl2_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f28,f54])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    ~spl2_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f24,f49])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f19,f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.45    inference(flattening,[],[f10])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,negated_conjecture,(
% 0.22/0.45    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.22/0.45    inference(negated_conjecture,[],[f8])).
% 0.22/0.45  fof(f8,conjecture,(
% 0.22/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    spl2_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f23,f44])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    r1_tarski(sK0,sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    spl2_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f22,f39])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    v1_relat_1(sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    spl2_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f21,f34])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    v1_relat_1(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (23300)------------------------------
% 0.22/0.45  % (23300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (23300)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (23300)Memory used [KB]: 6396
% 0.22/0.45  % (23300)Time elapsed: 0.042 s
% 0.22/0.45  % (23300)------------------------------
% 0.22/0.45  % (23300)------------------------------
% 0.22/0.46  % (23291)Success in time 0.094 s
%------------------------------------------------------------------------------
