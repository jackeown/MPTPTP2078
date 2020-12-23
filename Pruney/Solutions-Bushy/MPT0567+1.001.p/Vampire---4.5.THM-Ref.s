%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0567+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   59 (  90 expanded)
%              Number of leaves         :   16 (  42 expanded)
%              Depth                    :    5
%              Number of atoms          :  160 ( 246 expanded)
%              Number of equality atoms :   33 (  50 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f143,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f32,f36,f40,f44,f51,f76,f89,f101,f116,f136,f142])).

fof(f142,plain,
    ( ~ spl4_3
    | spl4_6
    | ~ spl4_23 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | ~ spl4_3
    | spl4_6
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f139,f50])).

fof(f50,plain,
    ( o_0_0_xboole_0 != k10_relat_1(sK0,o_0_0_xboole_0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl4_6
  <=> o_0_0_xboole_0 = k10_relat_1(sK0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f139,plain,
    ( o_0_0_xboole_0 = k10_relat_1(sK0,o_0_0_xboole_0)
    | ~ spl4_3
    | ~ spl4_23 ),
    inference(resolution,[],[f135,f35])).

fof(f35,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl4_3
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f135,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | k10_relat_1(sK0,o_0_0_xboole_0) = X2 )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl4_23
  <=> ! [X2] :
        ( k10_relat_1(sK0,o_0_0_xboole_0) = X2
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f136,plain,
    ( spl4_23
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f122,f114,f42,f134])).

fof(f42,plain,
    ( spl4_5
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f114,plain,
    ( spl4_20
  <=> ! [X0] :
        ( k10_relat_1(sK0,o_0_0_xboole_0) = X0
        | r2_hidden(sK1(sK0,o_0_0_xboole_0,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f122,plain,
    ( ! [X2] :
        ( k10_relat_1(sK0,o_0_0_xboole_0) = X2
        | ~ v1_xboole_0(X2) )
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(resolution,[],[f115,f43])).

fof(f43,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ v1_xboole_0(X1) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f115,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(sK0,o_0_0_xboole_0,X0),X0)
        | k10_relat_1(sK0,o_0_0_xboole_0) = X0 )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,
    ( spl4_20
    | ~ spl4_3
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f105,f99,f34,f114])).

fof(f99,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( r2_hidden(sK1(sK0,X0,X1),X1)
        | k10_relat_1(sK0,X0) = X1
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f105,plain,
    ( ! [X0] :
        ( k10_relat_1(sK0,o_0_0_xboole_0) = X0
        | r2_hidden(sK1(sK0,o_0_0_xboole_0,X0),X0) )
    | ~ spl4_3
    | ~ spl4_17 ),
    inference(resolution,[],[f100,f35])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | k10_relat_1(sK0,X0) = X1
        | r2_hidden(sK1(sK0,X0,X1),X1) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f99])).

fof(f101,plain,
    ( spl4_17
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f90,f87,f42,f99])).

fof(f87,plain,
    ( spl4_15
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(sK0,X0,X1),X0)
        | r2_hidden(sK1(sK0,X0,X1),X1)
        | k10_relat_1(sK0,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK1(sK0,X0,X1),X1)
        | k10_relat_1(sK0,X0) = X1
        | ~ v1_xboole_0(X0) )
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(resolution,[],[f88,f43])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK0,X0,X1),X0)
        | r2_hidden(sK1(sK0,X0,X1),X1)
        | k10_relat_1(sK0,X0) = X1 )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f87])).

fof(f89,plain,
    ( spl4_15
    | ~ spl4_1
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f77,f74,f26,f87])).

fof(f26,plain,
    ( spl4_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f74,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(sK3(X0,X1,X2),X1)
        | r2_hidden(sK1(X0,X1,X2),X2)
        | k10_relat_1(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK0,X0,X1),X0)
        | r2_hidden(sK1(sK0,X0,X1),X1)
        | k10_relat_1(sK0,X0) = X1 )
    | ~ spl4_1
    | ~ spl4_12 ),
    inference(resolution,[],[f75,f27])).

fof(f27,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f75,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(sK3(X0,X1,X2),X1)
        | r2_hidden(sK1(X0,X1,X2),X2)
        | k10_relat_1(X0,X1) = X2 )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f74])).

fof(f76,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f16,f74])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f51,plain,
    ( ~ spl4_6
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f47,f38,f34,f30,f49])).

fof(f30,plain,
    ( spl4_2
  <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f38,plain,
    ( spl4_4
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f47,plain,
    ( o_0_0_xboole_0 != k10_relat_1(sK0,o_0_0_xboole_0)
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f31,f45])).

fof(f45,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f39,f35])).

fof(f39,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f31,plain,
    ( k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f44,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f21,f42])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f40,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f20,f38])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f36,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f13,f34])).

fof(f13,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f32,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f12,f30])).

fof(f12,plain,(
    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

fof(f28,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f11,f26])).

fof(f11,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------
