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
% DateTime   : Thu Dec  3 12:47:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 127 expanded)
%              Number of leaves         :   19 (  61 expanded)
%              Depth                    :    5
%              Number of atoms          :  278 ( 475 expanded)
%              Number of equality atoms :   42 (  66 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f167,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f32,f39,f43,f47,f67,f71,f91,f98,f104,f111,f115,f122,f160,f166])).

fof(f166,plain,
    ( ~ spl6_2
    | spl6_3
    | ~ spl6_25 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | ~ spl6_2
    | spl6_3
    | ~ spl6_25 ),
    inference(unit_resulting_resolution,[],[f31,f31,f35,f159])).

fof(f159,plain,
    ( ! [X2,X1] :
        ( ~ v1_xboole_0(X1)
        | k5_relat_1(sK0,X1) = X2
        | ~ v1_xboole_0(X2) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl6_25
  <=> ! [X1,X2] :
        ( k5_relat_1(sK0,X1) = X2
        | ~ v1_xboole_0(X1)
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f35,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl6_3
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f31,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl6_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f160,plain,
    ( spl6_25
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f118,f113,f45,f41,f158])).

fof(f41,plain,
    ( spl6_5
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f45,plain,
    ( spl6_6
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f113,plain,
    ( spl6_19
  <=> ! [X1,X2] :
        ( ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(sK1(sK0,X2,X1),sK2(sK0,X2,X1)),X1)
        | k5_relat_1(sK0,X2) = X1
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f118,plain,
    ( ! [X2,X1] :
        ( k5_relat_1(sK0,X1) = X2
        | ~ v1_xboole_0(X1)
        | ~ v1_xboole_0(X2) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f117,f46])).

fof(f46,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f117,plain,
    ( ! [X2,X1] :
        ( r2_hidden(k4_tarski(sK1(sK0,X1,X2),sK2(sK0,X1,X2)),X2)
        | k5_relat_1(sK0,X1) = X2
        | ~ v1_xboole_0(X1)
        | ~ v1_xboole_0(X2) )
    | ~ spl6_5
    | ~ spl6_19 ),
    inference(resolution,[],[f114,f42])).

fof(f42,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f114,plain,
    ( ! [X2,X1] :
        ( ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(sK1(sK0,X2,X1),sK2(sK0,X2,X1)),X1)
        | k5_relat_1(sK0,X2) = X1
        | ~ v1_xboole_0(X2) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f113])).

fof(f122,plain,
    ( ~ spl6_2
    | spl6_4
    | ~ spl6_18 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | ~ spl6_2
    | spl6_4
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f31,f31,f38,f110])).

fof(f110,plain,
    ( ! [X2,X1] :
        ( ~ v1_xboole_0(X1)
        | k5_relat_1(X1,sK0) = X2
        | ~ v1_xboole_0(X2) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl6_18
  <=> ! [X1,X2] :
        ( k5_relat_1(X1,sK0) = X2
        | ~ v1_xboole_0(X1)
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f38,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl6_4
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f115,plain,
    ( spl6_19
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f94,f89,f45,f41,f113])).

fof(f89,plain,
    ( spl6_15
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(sK4(sK0,X0,X1),sK2(sK0,X0,X1)),X0)
        | r2_hidden(k4_tarski(sK1(sK0,X0,X1),sK2(sK0,X0,X1)),X1)
        | k5_relat_1(sK0,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f94,plain,
    ( ! [X2,X1] :
        ( ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(sK1(sK0,X2,X1),sK2(sK0,X2,X1)),X1)
        | k5_relat_1(sK0,X2) = X1
        | ~ v1_xboole_0(X2) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f93,f46])).

fof(f93,plain,
    ( ! [X2,X1] :
        ( ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(sK4(sK0,X2,X1),sK2(sK0,X2,X1)),X2)
        | r2_hidden(k4_tarski(sK1(sK0,X2,X1),sK2(sK0,X2,X1)),X1)
        | k5_relat_1(sK0,X2) = X1
        | ~ v1_xboole_0(X2) )
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(resolution,[],[f90,f42])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(sK4(sK0,X0,X1),sK2(sK0,X0,X1)),X0)
        | r2_hidden(k4_tarski(sK1(sK0,X0,X1),sK2(sK0,X0,X1)),X1)
        | k5_relat_1(sK0,X0) = X1 )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f89])).

fof(f111,plain,
    ( spl6_18
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f107,f102,f45,f41,f109])).

fof(f102,plain,
    ( spl6_17
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK1(X1,sK0,X0),sK2(X1,sK0,X0)),X0)
        | k5_relat_1(X1,sK0) = X0
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f107,plain,
    ( ! [X2,X1] :
        ( k5_relat_1(X1,sK0) = X2
        | ~ v1_xboole_0(X1)
        | ~ v1_xboole_0(X2) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f106,f46])).

fof(f106,plain,
    ( ! [X2,X1] :
        ( r2_hidden(k4_tarski(sK1(X1,sK0,X2),sK2(X1,sK0,X2)),X2)
        | k5_relat_1(X1,sK0) = X2
        | ~ v1_xboole_0(X1)
        | ~ v1_xboole_0(X2) )
    | ~ spl6_5
    | ~ spl6_17 ),
    inference(resolution,[],[f103,f42])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK1(X1,sK0,X0),sK2(X1,sK0,X0)),X0)
        | k5_relat_1(X1,sK0) = X0
        | ~ v1_xboole_0(X1) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f102])).

fof(f104,plain,
    ( spl6_17
    | ~ spl6_1
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f99,f96,f26,f102])).

fof(f26,plain,
    ( spl6_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f96,plain,
    ( spl6_16
  <=> ! [X3,X2,X4] :
        ( ~ v1_relat_1(X2)
        | ~ v1_relat_1(X3)
        | r2_hidden(k4_tarski(sK1(X4,X2,X3),sK2(X4,X2,X3)),X3)
        | k5_relat_1(X4,X2) = X3
        | ~ v1_xboole_0(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK1(X1,sK0,X0),sK2(X1,sK0,X0)),X0)
        | k5_relat_1(X1,sK0) = X0
        | ~ v1_xboole_0(X1) )
    | ~ spl6_1
    | ~ spl6_16 ),
    inference(resolution,[],[f97,f27])).

fof(f27,plain,
    ( v1_relat_1(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f97,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_relat_1(X2)
        | ~ v1_relat_1(X3)
        | r2_hidden(k4_tarski(sK1(X4,X2,X3),sK2(X4,X2,X3)),X3)
        | k5_relat_1(X4,X2) = X3
        | ~ v1_xboole_0(X4) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f96])).

fof(f98,plain,
    ( spl6_16
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f74,f65,f45,f41,f96])).

fof(f65,plain,
    ( spl6_11
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK4(X0,X1,X2)),X0)
        | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
        | k5_relat_1(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f74,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_relat_1(X2)
        | ~ v1_relat_1(X3)
        | r2_hidden(k4_tarski(sK1(X4,X2,X3),sK2(X4,X2,X3)),X3)
        | k5_relat_1(X4,X2) = X3
        | ~ v1_xboole_0(X4) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f73,f46])).

fof(f73,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_relat_1(X2)
        | ~ v1_relat_1(X3)
        | r2_hidden(k4_tarski(sK1(X4,X2,X3),sK4(X4,X2,X3)),X4)
        | r2_hidden(k4_tarski(sK1(X4,X2,X3),sK2(X4,X2,X3)),X3)
        | k5_relat_1(X4,X2) = X3
        | ~ v1_xboole_0(X4) )
    | ~ spl6_5
    | ~ spl6_11 ),
    inference(resolution,[],[f66,f42])).

fof(f66,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK4(X0,X1,X2)),X0)
        | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
        | k5_relat_1(X0,X1) = X2 )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f65])).

fof(f91,plain,
    ( spl6_15
    | ~ spl6_1
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f75,f69,f26,f89])).

fof(f69,plain,
    ( spl6_12
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK2(X0,X1,X2)),X1)
        | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
        | k5_relat_1(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(sK4(sK0,X0,X1),sK2(sK0,X0,X1)),X0)
        | r2_hidden(k4_tarski(sK1(sK0,X0,X1),sK2(sK0,X0,X1)),X1)
        | k5_relat_1(sK0,X0) = X1 )
    | ~ spl6_1
    | ~ spl6_12 ),
    inference(resolution,[],[f70,f27])).

fof(f70,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK2(X0,X1,X2)),X1)
        | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
        | k5_relat_1(X0,X1) = X2 )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f69])).

fof(f71,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f16,f69])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK2(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
      | k5_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f67,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f15,f65])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
      | k5_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f47,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f43,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f13,f41])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f39,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f10,f37,f34])).

fof(f10,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f32,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f12,f30])).

fof(f12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f28,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f11,f26])).

fof(f11,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (9999)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.46  % (9991)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.46  % (9999)Refutation not found, incomplete strategy% (9999)------------------------------
% 0.20/0.46  % (9999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (9999)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (9999)Memory used [KB]: 6140
% 0.20/0.47  % (9999)Time elapsed: 0.058 s
% 0.20/0.47  % (9999)------------------------------
% 0.20/0.47  % (9999)------------------------------
% 0.20/0.48  % (9989)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (9994)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.48  % (9994)Refutation not found, incomplete strategy% (9994)------------------------------
% 0.20/0.48  % (9994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (9994)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (9994)Memory used [KB]: 6012
% 0.20/0.48  % (9994)Time elapsed: 0.075 s
% 0.20/0.48  % (9994)------------------------------
% 0.20/0.48  % (9994)------------------------------
% 0.20/0.48  % (9993)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  % (9986)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (9993)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f167,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f28,f32,f39,f43,f47,f67,f71,f91,f98,f104,f111,f115,f122,f160,f166])).
% 0.20/0.48  fof(f166,plain,(
% 0.20/0.48    ~spl6_2 | spl6_3 | ~spl6_25),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f163])).
% 0.20/0.48  fof(f163,plain,(
% 0.20/0.48    $false | (~spl6_2 | spl6_3 | ~spl6_25)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f31,f31,f35,f159])).
% 0.20/0.48  fof(f159,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~v1_xboole_0(X1) | k5_relat_1(sK0,X1) = X2 | ~v1_xboole_0(X2)) ) | ~spl6_25),
% 0.20/0.48    inference(avatar_component_clause,[],[f158])).
% 0.20/0.48  fof(f158,plain,(
% 0.20/0.48    spl6_25 <=> ! [X1,X2] : (k5_relat_1(sK0,X1) = X2 | ~v1_xboole_0(X1) | ~v1_xboole_0(X2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl6_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    spl6_3 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0) | ~spl6_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    spl6_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    spl6_25 | ~spl6_5 | ~spl6_6 | ~spl6_19),
% 0.20/0.48    inference(avatar_split_clause,[],[f118,f113,f45,f41,f158])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    spl6_5 <=> ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    spl6_6 <=> ! [X1,X0] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    spl6_19 <=> ! [X1,X2] : (~v1_relat_1(X1) | r2_hidden(k4_tarski(sK1(sK0,X2,X1),sK2(sK0,X2,X1)),X1) | k5_relat_1(sK0,X2) = X1 | ~v1_xboole_0(X2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    ( ! [X2,X1] : (k5_relat_1(sK0,X1) = X2 | ~v1_xboole_0(X1) | ~v1_xboole_0(X2)) ) | (~spl6_5 | ~spl6_6 | ~spl6_19)),
% 0.20/0.48    inference(subsumption_resolution,[],[f117,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) ) | ~spl6_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f45])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    ( ! [X2,X1] : (r2_hidden(k4_tarski(sK1(sK0,X1,X2),sK2(sK0,X1,X2)),X2) | k5_relat_1(sK0,X1) = X2 | ~v1_xboole_0(X1) | ~v1_xboole_0(X2)) ) | (~spl6_5 | ~spl6_19)),
% 0.20/0.48    inference(resolution,[],[f114,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) ) | ~spl6_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f41])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~v1_relat_1(X1) | r2_hidden(k4_tarski(sK1(sK0,X2,X1),sK2(sK0,X2,X1)),X1) | k5_relat_1(sK0,X2) = X1 | ~v1_xboole_0(X2)) ) | ~spl6_19),
% 0.20/0.48    inference(avatar_component_clause,[],[f113])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    ~spl6_2 | spl6_4 | ~spl6_18),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f119])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    $false | (~spl6_2 | spl6_4 | ~spl6_18)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f31,f31,f38,f110])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~v1_xboole_0(X1) | k5_relat_1(X1,sK0) = X2 | ~v1_xboole_0(X2)) ) | ~spl6_18),
% 0.20/0.48    inference(avatar_component_clause,[],[f109])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    spl6_18 <=> ! [X1,X2] : (k5_relat_1(X1,sK0) = X2 | ~v1_xboole_0(X1) | ~v1_xboole_0(X2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl6_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    spl6_4 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    spl6_19 | ~spl6_5 | ~spl6_6 | ~spl6_15),
% 0.20/0.48    inference(avatar_split_clause,[],[f94,f89,f45,f41,f113])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    spl6_15 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(sK4(sK0,X0,X1),sK2(sK0,X0,X1)),X0) | r2_hidden(k4_tarski(sK1(sK0,X0,X1),sK2(sK0,X0,X1)),X1) | k5_relat_1(sK0,X0) = X1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~v1_relat_1(X1) | r2_hidden(k4_tarski(sK1(sK0,X2,X1),sK2(sK0,X2,X1)),X1) | k5_relat_1(sK0,X2) = X1 | ~v1_xboole_0(X2)) ) | (~spl6_5 | ~spl6_6 | ~spl6_15)),
% 0.20/0.48    inference(subsumption_resolution,[],[f93,f46])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~v1_relat_1(X1) | r2_hidden(k4_tarski(sK4(sK0,X2,X1),sK2(sK0,X2,X1)),X2) | r2_hidden(k4_tarski(sK1(sK0,X2,X1),sK2(sK0,X2,X1)),X1) | k5_relat_1(sK0,X2) = X1 | ~v1_xboole_0(X2)) ) | (~spl6_5 | ~spl6_15)),
% 0.20/0.48    inference(resolution,[],[f90,f42])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(sK4(sK0,X0,X1),sK2(sK0,X0,X1)),X0) | r2_hidden(k4_tarski(sK1(sK0,X0,X1),sK2(sK0,X0,X1)),X1) | k5_relat_1(sK0,X0) = X1) ) | ~spl6_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f89])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    spl6_18 | ~spl6_5 | ~spl6_6 | ~spl6_17),
% 0.20/0.48    inference(avatar_split_clause,[],[f107,f102,f45,f41,f109])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    spl6_17 <=> ! [X1,X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK1(X1,sK0,X0),sK2(X1,sK0,X0)),X0) | k5_relat_1(X1,sK0) = X0 | ~v1_xboole_0(X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    ( ! [X2,X1] : (k5_relat_1(X1,sK0) = X2 | ~v1_xboole_0(X1) | ~v1_xboole_0(X2)) ) | (~spl6_5 | ~spl6_6 | ~spl6_17)),
% 0.20/0.48    inference(subsumption_resolution,[],[f106,f46])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    ( ! [X2,X1] : (r2_hidden(k4_tarski(sK1(X1,sK0,X2),sK2(X1,sK0,X2)),X2) | k5_relat_1(X1,sK0) = X2 | ~v1_xboole_0(X1) | ~v1_xboole_0(X2)) ) | (~spl6_5 | ~spl6_17)),
% 0.20/0.48    inference(resolution,[],[f103,f42])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK1(X1,sK0,X0),sK2(X1,sK0,X0)),X0) | k5_relat_1(X1,sK0) = X0 | ~v1_xboole_0(X1)) ) | ~spl6_17),
% 0.20/0.48    inference(avatar_component_clause,[],[f102])).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    spl6_17 | ~spl6_1 | ~spl6_16),
% 0.20/0.48    inference(avatar_split_clause,[],[f99,f96,f26,f102])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    spl6_1 <=> v1_relat_1(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    spl6_16 <=> ! [X3,X2,X4] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | r2_hidden(k4_tarski(sK1(X4,X2,X3),sK2(X4,X2,X3)),X3) | k5_relat_1(X4,X2) = X3 | ~v1_xboole_0(X4))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK1(X1,sK0,X0),sK2(X1,sK0,X0)),X0) | k5_relat_1(X1,sK0) = X0 | ~v1_xboole_0(X1)) ) | (~spl6_1 | ~spl6_16)),
% 0.20/0.48    inference(resolution,[],[f97,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    v1_relat_1(sK0) | ~spl6_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f26])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | r2_hidden(k4_tarski(sK1(X4,X2,X3),sK2(X4,X2,X3)),X3) | k5_relat_1(X4,X2) = X3 | ~v1_xboole_0(X4)) ) | ~spl6_16),
% 0.20/0.48    inference(avatar_component_clause,[],[f96])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    spl6_16 | ~spl6_5 | ~spl6_6 | ~spl6_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f74,f65,f45,f41,f96])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    spl6_11 <=> ! [X1,X0,X2] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK4(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | k5_relat_1(X0,X1) = X2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | r2_hidden(k4_tarski(sK1(X4,X2,X3),sK2(X4,X2,X3)),X3) | k5_relat_1(X4,X2) = X3 | ~v1_xboole_0(X4)) ) | (~spl6_5 | ~spl6_6 | ~spl6_11)),
% 0.20/0.48    inference(subsumption_resolution,[],[f73,f46])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | r2_hidden(k4_tarski(sK1(X4,X2,X3),sK4(X4,X2,X3)),X4) | r2_hidden(k4_tarski(sK1(X4,X2,X3),sK2(X4,X2,X3)),X3) | k5_relat_1(X4,X2) = X3 | ~v1_xboole_0(X4)) ) | (~spl6_5 | ~spl6_11)),
% 0.20/0.48    inference(resolution,[],[f66,f42])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK4(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | k5_relat_1(X0,X1) = X2) ) | ~spl6_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f65])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    spl6_15 | ~spl6_1 | ~spl6_12),
% 0.20/0.48    inference(avatar_split_clause,[],[f75,f69,f26,f89])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    spl6_12 <=> ! [X1,X0,X2] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK2(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | k5_relat_1(X0,X1) = X2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(sK4(sK0,X0,X1),sK2(sK0,X0,X1)),X0) | r2_hidden(k4_tarski(sK1(sK0,X0,X1),sK2(sK0,X0,X1)),X1) | k5_relat_1(sK0,X0) = X1) ) | (~spl6_1 | ~spl6_12)),
% 0.20/0.48    inference(resolution,[],[f70,f27])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK2(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | k5_relat_1(X0,X1) = X2) ) | ~spl6_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f69])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    spl6_12),
% 0.20/0.48    inference(avatar_split_clause,[],[f16,f69])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK2(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | k5_relat_1(X0,X1) = X2) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    spl6_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f15,f65])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK4(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | k5_relat_1(X0,X1) = X2) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    spl6_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f21,f45])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    spl6_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f13,f41])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ~spl6_3 | ~spl6_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f10,f37,f34])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,negated_conjecture,(
% 0.20/0.48    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.48    inference(negated_conjecture,[],[f5])).
% 0.20/0.48  fof(f5,conjecture,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    spl6_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f12,f30])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    spl6_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f11,f26])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    v1_relat_1(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (9993)------------------------------
% 0.20/0.48  % (9993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (9993)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (9993)Memory used [KB]: 10746
% 0.20/0.48  % (9993)Time elapsed: 0.076 s
% 0.20/0.48  % (9993)------------------------------
% 0.20/0.48  % (9993)------------------------------
% 0.20/0.49  % (9983)Success in time 0.131 s
%------------------------------------------------------------------------------
