%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t50_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:28 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 117 expanded)
%              Number of leaves         :   13 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :  184 ( 349 expanded)
%              Number of equality atoms :   14 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f165,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f75,f83,f87,f91,f138,f145,f151,f158,f164])).

fof(f164,plain,
    ( spl3_5
    | spl3_7
    | ~ spl3_26 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f162,f82])).

fof(f82,plain,
    ( ~ r2_xboole_0(sK0,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_5
  <=> ~ r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f162,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl3_7
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f161,f86])).

fof(f86,plain,
    ( sK0 != sK1
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_7
  <=> sK0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f161,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK0,sK1)
    | ~ spl3_26 ),
    inference(resolution,[],[f157,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t50_ordinal1.p',d8_xboole_0)).

fof(f157,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl3_26
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f158,plain,
    ( spl3_26
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f154,f133,f73,f69,f156])).

fof(f69,plain,
    ( spl3_0
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f73,plain,
    ( spl3_2
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f133,plain,
    ( spl3_20
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f154,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f153,f74])).

fof(f74,plain,
    ( v3_ordinal1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f153,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl3_0
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f152,f70])).

fof(f70,plain,
    ( v3_ordinal1(sK1)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f69])).

fof(f152,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl3_20 ),
    inference(resolution,[],[f134,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t50_ordinal1.p',redefinition_r1_ordinal1)).

fof(f134,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f133])).

fof(f151,plain,
    ( spl3_7
    | spl3_9
    | ~ spl3_24 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f149,f90])).

fof(f90,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_9
  <=> ~ r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f149,plain,
    ( r2_xboole_0(sK1,sK0)
    | ~ spl3_7
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f148,f86])).

fof(f148,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK1,sK0)
    | ~ spl3_24 ),
    inference(resolution,[],[f144,f51])).

fof(f144,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl3_24
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f145,plain,
    ( spl3_24
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f141,f136,f73,f69,f143])).

fof(f136,plain,
    ( spl3_22
  <=> r1_ordinal1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f141,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f140,f70])).

fof(f140,plain,
    ( r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl3_2
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f139,f74])).

fof(f139,plain,
    ( ~ v3_ordinal1(sK0)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl3_22 ),
    inference(resolution,[],[f137,f55])).

fof(f137,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f136])).

fof(f138,plain,
    ( spl3_20
    | spl3_22
    | ~ spl3_0
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f111,f73,f69,f136,f133])).

fof(f111,plain,
    ( r1_ordinal1(sK1,sK0)
    | r1_ordinal1(sK0,sK1)
    | ~ spl3_0
    | ~ spl3_2 ),
    inference(resolution,[],[f77,f74])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r1_ordinal1(sK1,X0)
        | r1_ordinal1(X0,sK1) )
    | ~ spl3_0 ),
    inference(resolution,[],[f70,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r1_ordinal1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t50_ordinal1.p',connectedness_r1_ordinal1)).

fof(f91,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f48,f89])).

fof(f48,plain,(
    ~ r2_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ~ ( ~ r2_xboole_0(X1,X0)
                & X0 != X1
                & ~ r2_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_xboole_0(X1,X0)
              & X0 != X1
              & ~ r2_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t50_ordinal1.p',t50_ordinal1)).

fof(f87,plain,(
    ~ spl3_7 ),
    inference(avatar_split_clause,[],[f47,f85])).

fof(f47,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f83,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f46,f81])).

fof(f46,plain,(
    ~ r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f49,f73])).

fof(f49,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f71,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f45,f69])).

fof(f45,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
