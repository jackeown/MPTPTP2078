%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:03 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 242 expanded)
%              Number of leaves         :   27 (  84 expanded)
%              Depth                    :   12
%              Number of atoms          :  449 ( 799 expanded)
%              Number of equality atoms :   31 (  61 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f424,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f82,f99,f109,f127,f129,f166,f171,f197,f203,f250,f254,f355,f374,f383,f407,f423])).

fof(f423,plain,
    ( ~ spl9_1
    | ~ spl9_7
    | ~ spl9_21 ),
    inference(avatar_contradiction_clause,[],[f422])).

fof(f422,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_7
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f420,f417])).

fof(f417,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl9_1
    | ~ spl9_21 ),
    inference(resolution,[],[f406,f90])).

fof(f90,plain,
    ( ! [X12,X11] :
        ( ~ sP7(X11,X12,sK2)
        | r2_hidden(X11,k1_wellord1(sK2,X12)) )
    | ~ spl9_1 ),
    inference(resolution,[],[f76,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP7(X3,X1,X0)
      | r2_hidden(X3,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(f76,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl9_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f406,plain,
    ( sP7(sK1,sK0,sK2)
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f404])).

fof(f404,plain,
    ( spl9_21
  <=> sP7(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f420,plain,
    ( ~ r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl9_1
    | ~ spl9_7 ),
    inference(resolution,[],[f126,f151])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k1_wellord1(sK2,X0))
        | ~ r2_hidden(X0,X1) )
    | ~ spl9_1 ),
    inference(resolution,[],[f149,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f149,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_wellord1(sK2,X0))
    | ~ spl9_1 ),
    inference(resolution,[],[f89,f70])).

fof(f70,plain,(
    ! [X0,X3] : ~ sP7(X3,X3,X0) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( X1 != X3
      | ~ sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f89,plain,
    ( ! [X10,X9] :
        ( sP7(X9,X10,sK2)
        | ~ r2_hidden(X9,k1_wellord1(sK2,X10)) )
    | ~ spl9_1 ),
    inference(resolution,[],[f76,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sP7(X3,X1,X0)
      | ~ r2_hidden(X3,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f126,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl9_7
  <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f407,plain,
    ( spl9_21
    | ~ spl9_3
    | ~ spl9_5
    | spl9_6
    | ~ spl9_15
    | spl9_16 ),
    inference(avatar_split_clause,[],[f398,f223,f195,f120,f106,f96,f404])).

fof(f96,plain,
    ( spl9_3
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f106,plain,
    ( spl9_5
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f120,plain,
    ( spl9_6
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f195,plain,
    ( spl9_15
  <=> ! [X1,X2] :
        ( ~ r2_hidden(X1,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X2,X1),sK2)
        | r2_hidden(k4_tarski(X1,X2),sK2)
        | X1 = X2
        | ~ r2_hidden(X2,k3_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f223,plain,
    ( spl9_16
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f398,plain,
    ( sP7(sK1,sK0,sK2)
    | ~ spl9_3
    | ~ spl9_5
    | spl9_6
    | ~ spl9_15
    | spl9_16 ),
    inference(subsumption_resolution,[],[f397,f108])).

fof(f108,plain,
    ( r2_hidden(sK1,k3_relat_1(sK2))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f397,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK2))
    | sP7(sK1,sK0,sK2)
    | ~ spl9_3
    | spl9_6
    | ~ spl9_15
    | spl9_16 ),
    inference(subsumption_resolution,[],[f396,f224])).

fof(f224,plain,
    ( sK0 != sK1
    | spl9_16 ),
    inference(avatar_component_clause,[],[f223])).

fof(f396,plain,
    ( sK0 = sK1
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | sP7(sK1,sK0,sK2)
    | ~ spl9_3
    | spl9_6
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f392,f98])).

fof(f98,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f392,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | sK0 = sK1
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | sP7(sK1,sK0,sK2)
    | spl9_6
    | ~ spl9_15 ),
    inference(resolution,[],[f121,f219])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | X0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | sP7(X1,X0,sK2) )
    | ~ spl9_15 ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1
        | sP7(X1,X0,sK2) )
    | ~ spl9_15 ),
    inference(resolution,[],[f196,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X1),X0)
      | X1 = X3
      | sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f196,plain,
    ( ! [X2,X1] :
        ( r2_hidden(k4_tarski(X2,X1),sK2)
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X1,X2),sK2)
        | X1 = X2
        | ~ r2_hidden(X2,k3_relat_1(sK2)) )
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f195])).

fof(f121,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | spl9_6 ),
    inference(avatar_component_clause,[],[f120])).

fof(f383,plain,
    ( ~ spl9_3
    | ~ spl9_11
    | spl9_20 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_11
    | spl9_20 ),
    inference(subsumption_resolution,[],[f375,f98])).

fof(f375,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl9_11
    | spl9_20 ),
    inference(resolution,[],[f373,f165])).

fof(f165,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2)) )
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl9_11
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X0,X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f373,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK0),sK2)
    | spl9_20 ),
    inference(avatar_component_clause,[],[f371])).

fof(f371,plain,
    ( spl9_20
  <=> r2_hidden(k4_tarski(sK0,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f374,plain,
    ( ~ spl9_20
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f363,f223,f371])).

fof(f363,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK0),sK2)
    | ~ spl9_16 ),
    inference(forward_demodulation,[],[f362,f225])).

fof(f225,plain,
    ( sK0 = sK1
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f223])).

fof(f362,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f357,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
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

fof(f357,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl9_16 ),
    inference(backward_demodulation,[],[f29,f225])).

fof(f29,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => ( r2_hidden(k4_tarski(X0,X1),X2)
          <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).

fof(f355,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | spl9_7
    | ~ spl9_9 ),
    inference(avatar_contradiction_clause,[],[f354])).

fof(f354,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | spl9_7
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f352,f88])).

fof(f88,plain,
    ( ! [X8] : r1_tarski(k3_relat_1(k2_wellord1(sK2,X8)),X8)
    | ~ spl9_1 ),
    inference(resolution,[],[f76,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_wellord1)).

fof(f352,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))),k1_wellord1(sK2,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | spl9_7
    | ~ spl9_9 ),
    inference(resolution,[],[f294,f156])).

fof(f156,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl9_9
  <=> r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f294,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK0,k1_wellord1(sK2,X2))
        | ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X2))),k1_wellord1(sK2,sK1)) )
    | ~ spl9_1
    | ~ spl9_2
    | spl9_7 ),
    inference(resolution,[],[f186,f247])).

fof(f247,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_wellord1(sK2,sK0),X0)
        | ~ r1_tarski(X0,k1_wellord1(sK2,sK1)) )
    | spl9_7 ),
    inference(resolution,[],[f125,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f125,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | spl9_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f186,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_wellord1(sK2,X1),k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X0))))
        | ~ r2_hidden(X1,k1_wellord1(sK2,X0)) )
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f185,f87])).

fof(f87,plain,
    ( ! [X7] : v1_relat_1(k2_wellord1(sK2,X7))
    | ~ spl9_1 ),
    inference(resolution,[],[f76,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k2_wellord1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f185,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_wellord1(sK2,X1),k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X0))))
        | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X0)))
        | ~ r2_hidden(X1,k1_wellord1(sK2,X0)) )
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(superposition,[],[f57,f93])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( k1_wellord1(sK2,X0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),X0)
        | ~ r2_hidden(X0,k1_wellord1(sK2,X1)) )
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f91,f76])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(X0,k1_wellord1(sK2,X1))
        | k1_wellord1(sK2,X0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),X0) )
    | ~ spl9_2 ),
    inference(resolution,[],[f81,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X0,k1_wellord1(X2,X1))
          & v2_wellord1(X2) )
       => k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_wellord1)).

fof(f81,plain,
    ( v2_wellord1(sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl9_2
  <=> v2_wellord1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).

fof(f254,plain,
    ( spl9_9
    | ~ spl9_1
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f251,f133,f74,f155])).

fof(f133,plain,
    ( spl9_8
  <=> sP7(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f251,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl9_1
    | ~ spl9_8 ),
    inference(resolution,[],[f134,f90])).

fof(f134,plain,
    ( sP7(sK0,sK1,sK2)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f250,plain,
    ( spl9_8
    | spl9_16
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f232,f120,f223,f133])).

fof(f232,plain,
    ( sK0 = sK1
    | sP7(sK0,sK1,sK2)
    | ~ spl9_6 ),
    inference(resolution,[],[f122,f49])).

fof(f122,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f120])).

fof(f203,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | spl9_14 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | spl9_14 ),
    inference(subsumption_resolution,[],[f201,f81])).

fof(f201,plain,
    ( ~ v2_wellord1(sK2)
    | ~ spl9_1
    | spl9_14 ),
    inference(subsumption_resolution,[],[f198,f76])).

fof(f198,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v2_wellord1(sK2)
    | spl9_14 ),
    inference(resolution,[],[f193,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(f193,plain,
    ( ~ v6_relat_2(sK2)
    | spl9_14 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl9_14
  <=> v6_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f197,plain,
    ( ~ spl9_14
    | spl9_15
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f84,f74,f195,f191])).

fof(f84,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X2,k3_relat_1(sK2))
        | X1 = X2
        | r2_hidden(k4_tarski(X1,X2),sK2)
        | r2_hidden(k4_tarski(X2,X1),sK2)
        | ~ v6_relat_2(sK2) )
    | ~ spl9_1 ),
    inference(resolution,[],[f76,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | X1 = X2
      | r2_hidden(k4_tarski(X1,X2),X0)
      | r2_hidden(k4_tarski(X2,X1),X0)
      | ~ v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).

fof(f171,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | spl9_10 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | spl9_10 ),
    inference(subsumption_resolution,[],[f169,f81])).

fof(f169,plain,
    ( ~ v2_wellord1(sK2)
    | ~ spl9_1
    | spl9_10 ),
    inference(subsumption_resolution,[],[f167,f76])).

fof(f167,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v2_wellord1(sK2)
    | spl9_10 ),
    inference(resolution,[],[f162,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f162,plain,
    ( ~ v1_relat_2(sK2)
    | spl9_10 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl9_10
  <=> v1_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f166,plain,
    ( ~ spl9_10
    | spl9_11
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f83,f74,f164,f160])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X0,X0),sK2)
        | ~ v1_relat_2(sK2) )
    | ~ spl9_1 ),
    inference(resolution,[],[f76,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | r2_hidden(k4_tarski(X1,X1),X0)
      | ~ v1_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

fof(f129,plain,
    ( ~ spl9_6
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f128,f124,f120])).

fof(f128,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f29,f126])).

fof(f127,plain,
    ( spl9_6
    | spl9_7 ),
    inference(avatar_split_clause,[],[f28,f124,f120])).

fof(f28,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f109,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f33,f106])).

fof(f33,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f99,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f32,f96])).

fof(f32,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f82,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f31,f79])).

fof(f31,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f77,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f30,f74])).

fof(f30,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (7925)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (7917)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (7909)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (7913)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (7923)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (7907)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (7912)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (7931)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (7904)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (7915)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (7908)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (7903)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (7930)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (7905)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (7906)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (7927)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (7914)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (7932)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (7918)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (7911)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (7924)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (7910)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (7922)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (7919)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (7929)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (7928)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (7926)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (7916)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (7920)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (7921)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.57/0.58  % (7923)Refutation found. Thanks to Tanya!
% 1.57/0.58  % SZS status Theorem for theBenchmark
% 1.57/0.58  % SZS output start Proof for theBenchmark
% 1.57/0.58  fof(f424,plain,(
% 1.57/0.58    $false),
% 1.57/0.58    inference(avatar_sat_refutation,[],[f77,f82,f99,f109,f127,f129,f166,f171,f197,f203,f250,f254,f355,f374,f383,f407,f423])).
% 1.57/0.58  fof(f423,plain,(
% 1.57/0.58    ~spl9_1 | ~spl9_7 | ~spl9_21),
% 1.57/0.58    inference(avatar_contradiction_clause,[],[f422])).
% 1.57/0.58  fof(f422,plain,(
% 1.57/0.58    $false | (~spl9_1 | ~spl9_7 | ~spl9_21)),
% 1.57/0.58    inference(subsumption_resolution,[],[f420,f417])).
% 1.57/0.58  fof(f417,plain,(
% 1.57/0.58    r2_hidden(sK1,k1_wellord1(sK2,sK0)) | (~spl9_1 | ~spl9_21)),
% 1.57/0.58    inference(resolution,[],[f406,f90])).
% 1.57/0.58  fof(f90,plain,(
% 1.57/0.58    ( ! [X12,X11] : (~sP7(X11,X12,sK2) | r2_hidden(X11,k1_wellord1(sK2,X12))) ) | ~spl9_1),
% 1.57/0.58    inference(resolution,[],[f76,f69])).
% 1.57/0.58  fof(f69,plain,(
% 1.57/0.58    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~sP7(X3,X1,X0) | r2_hidden(X3,k1_wellord1(X0,X1))) )),
% 1.57/0.58    inference(equality_resolution,[],[f52])).
% 1.57/0.58  fof(f52,plain,(
% 1.57/0.58    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~sP7(X3,X1,X0) | r2_hidden(X3,X2) | k1_wellord1(X0,X1) != X2) )),
% 1.57/0.58    inference(cnf_transformation,[],[f19])).
% 1.57/0.58  fof(f19,plain,(
% 1.57/0.58    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 1.57/0.58    inference(ennf_transformation,[],[f4])).
% 1.57/0.58  fof(f4,axiom,(
% 1.57/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).
% 1.57/0.58  fof(f76,plain,(
% 1.57/0.58    v1_relat_1(sK2) | ~spl9_1),
% 1.57/0.58    inference(avatar_component_clause,[],[f74])).
% 1.57/0.58  fof(f74,plain,(
% 1.57/0.58    spl9_1 <=> v1_relat_1(sK2)),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.57/0.58  fof(f406,plain,(
% 1.57/0.58    sP7(sK1,sK0,sK2) | ~spl9_21),
% 1.57/0.58    inference(avatar_component_clause,[],[f404])).
% 1.57/0.58  fof(f404,plain,(
% 1.57/0.58    spl9_21 <=> sP7(sK1,sK0,sK2)),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 1.57/0.58  fof(f420,plain,(
% 1.57/0.58    ~r2_hidden(sK1,k1_wellord1(sK2,sK0)) | (~spl9_1 | ~spl9_7)),
% 1.57/0.58    inference(resolution,[],[f126,f151])).
% 1.57/0.58  fof(f151,plain,(
% 1.57/0.58    ( ! [X0,X1] : (~r1_tarski(X1,k1_wellord1(sK2,X0)) | ~r2_hidden(X0,X1)) ) | ~spl9_1),
% 1.57/0.58    inference(resolution,[],[f149,f63])).
% 1.57/0.58  fof(f63,plain,(
% 1.57/0.58    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f23])).
% 1.57/0.58  fof(f23,plain,(
% 1.57/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.57/0.58    inference(ennf_transformation,[],[f1])).
% 1.57/0.58  fof(f1,axiom,(
% 1.57/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.57/0.58  fof(f149,plain,(
% 1.57/0.58    ( ! [X0] : (~r2_hidden(X0,k1_wellord1(sK2,X0))) ) | ~spl9_1),
% 1.57/0.58    inference(resolution,[],[f89,f70])).
% 1.57/0.58  fof(f70,plain,(
% 1.57/0.58    ( ! [X0,X3] : (~sP7(X3,X3,X0)) )),
% 1.57/0.58    inference(equality_resolution,[],[f50])).
% 1.57/0.58  fof(f50,plain,(
% 1.57/0.58    ( ! [X0,X3,X1] : (X1 != X3 | ~sP7(X3,X1,X0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f19])).
% 1.57/0.58  fof(f89,plain,(
% 1.57/0.58    ( ! [X10,X9] : (sP7(X9,X10,sK2) | ~r2_hidden(X9,k1_wellord1(sK2,X10))) ) | ~spl9_1),
% 1.57/0.58    inference(resolution,[],[f76,f68])).
% 1.57/0.58  fof(f68,plain,(
% 1.57/0.58    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | sP7(X3,X1,X0) | ~r2_hidden(X3,k1_wellord1(X0,X1))) )),
% 1.57/0.58    inference(equality_resolution,[],[f53])).
% 1.57/0.58  fof(f53,plain,(
% 1.57/0.58    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | sP7(X3,X1,X0) | ~r2_hidden(X3,X2) | k1_wellord1(X0,X1) != X2) )),
% 1.57/0.58    inference(cnf_transformation,[],[f19])).
% 1.57/0.58  fof(f126,plain,(
% 1.57/0.58    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl9_7),
% 1.57/0.58    inference(avatar_component_clause,[],[f124])).
% 1.57/0.58  fof(f124,plain,(
% 1.57/0.58    spl9_7 <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 1.57/0.58  fof(f407,plain,(
% 1.57/0.58    spl9_21 | ~spl9_3 | ~spl9_5 | spl9_6 | ~spl9_15 | spl9_16),
% 1.57/0.58    inference(avatar_split_clause,[],[f398,f223,f195,f120,f106,f96,f404])).
% 1.57/0.58  fof(f96,plain,(
% 1.57/0.58    spl9_3 <=> r2_hidden(sK0,k3_relat_1(sK2))),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.57/0.58  fof(f106,plain,(
% 1.57/0.58    spl9_5 <=> r2_hidden(sK1,k3_relat_1(sK2))),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.57/0.58  fof(f120,plain,(
% 1.57/0.58    spl9_6 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.57/0.58  fof(f195,plain,(
% 1.57/0.58    spl9_15 <=> ! [X1,X2] : (~r2_hidden(X1,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X2,X1),sK2) | r2_hidden(k4_tarski(X1,X2),sK2) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(sK2)))),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 1.57/0.58  fof(f223,plain,(
% 1.57/0.58    spl9_16 <=> sK0 = sK1),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 1.57/0.58  fof(f398,plain,(
% 1.57/0.58    sP7(sK1,sK0,sK2) | (~spl9_3 | ~spl9_5 | spl9_6 | ~spl9_15 | spl9_16)),
% 1.57/0.58    inference(subsumption_resolution,[],[f397,f108])).
% 1.57/0.58  fof(f108,plain,(
% 1.57/0.58    r2_hidden(sK1,k3_relat_1(sK2)) | ~spl9_5),
% 1.57/0.58    inference(avatar_component_clause,[],[f106])).
% 1.57/0.58  fof(f397,plain,(
% 1.57/0.58    ~r2_hidden(sK1,k3_relat_1(sK2)) | sP7(sK1,sK0,sK2) | (~spl9_3 | spl9_6 | ~spl9_15 | spl9_16)),
% 1.57/0.58    inference(subsumption_resolution,[],[f396,f224])).
% 1.57/0.58  fof(f224,plain,(
% 1.57/0.58    sK0 != sK1 | spl9_16),
% 1.57/0.58    inference(avatar_component_clause,[],[f223])).
% 1.57/0.58  fof(f396,plain,(
% 1.57/0.58    sK0 = sK1 | ~r2_hidden(sK1,k3_relat_1(sK2)) | sP7(sK1,sK0,sK2) | (~spl9_3 | spl9_6 | ~spl9_15)),
% 1.57/0.58    inference(subsumption_resolution,[],[f392,f98])).
% 1.57/0.58  fof(f98,plain,(
% 1.57/0.58    r2_hidden(sK0,k3_relat_1(sK2)) | ~spl9_3),
% 1.57/0.58    inference(avatar_component_clause,[],[f96])).
% 1.57/0.58  fof(f392,plain,(
% 1.57/0.58    ~r2_hidden(sK0,k3_relat_1(sK2)) | sK0 = sK1 | ~r2_hidden(sK1,k3_relat_1(sK2)) | sP7(sK1,sK0,sK2) | (spl9_6 | ~spl9_15)),
% 1.57/0.58    inference(resolution,[],[f121,f219])).
% 1.57/0.58  fof(f219,plain,(
% 1.57/0.58    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),sK2) | ~r2_hidden(X0,k3_relat_1(sK2)) | X0 = X1 | ~r2_hidden(X1,k3_relat_1(sK2)) | sP7(X1,X0,sK2)) ) | ~spl9_15),
% 1.57/0.58    inference(duplicate_literal_removal,[],[f215])).
% 1.57/0.58  fof(f215,plain,(
% 1.57/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X0,X1),sK2) | X0 = X1 | ~r2_hidden(X1,k3_relat_1(sK2)) | X0 = X1 | sP7(X1,X0,sK2)) ) | ~spl9_15),
% 1.57/0.58    inference(resolution,[],[f196,f49])).
% 1.57/0.58  fof(f49,plain,(
% 1.57/0.58    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | sP7(X3,X1,X0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f19])).
% 1.57/0.58  fof(f196,plain,(
% 1.57/0.58    ( ! [X2,X1] : (r2_hidden(k4_tarski(X2,X1),sK2) | ~r2_hidden(X1,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X1,X2),sK2) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(sK2))) ) | ~spl9_15),
% 1.57/0.58    inference(avatar_component_clause,[],[f195])).
% 1.57/0.58  fof(f121,plain,(
% 1.57/0.58    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | spl9_6),
% 1.57/0.58    inference(avatar_component_clause,[],[f120])).
% 1.57/0.58  fof(f383,plain,(
% 1.57/0.58    ~spl9_3 | ~spl9_11 | spl9_20),
% 1.57/0.58    inference(avatar_contradiction_clause,[],[f382])).
% 1.57/0.58  fof(f382,plain,(
% 1.57/0.58    $false | (~spl9_3 | ~spl9_11 | spl9_20)),
% 1.57/0.58    inference(subsumption_resolution,[],[f375,f98])).
% 1.57/0.58  fof(f375,plain,(
% 1.57/0.58    ~r2_hidden(sK0,k3_relat_1(sK2)) | (~spl9_11 | spl9_20)),
% 1.57/0.58    inference(resolution,[],[f373,f165])).
% 1.57/0.58  fof(f165,plain,(
% 1.57/0.58    ( ! [X0] : (r2_hidden(k4_tarski(X0,X0),sK2) | ~r2_hidden(X0,k3_relat_1(sK2))) ) | ~spl9_11),
% 1.57/0.58    inference(avatar_component_clause,[],[f164])).
% 1.57/0.58  fof(f164,plain,(
% 1.57/0.58    spl9_11 <=> ! [X0] : (~r2_hidden(X0,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X0,X0),sK2))),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 1.57/0.58  fof(f373,plain,(
% 1.57/0.58    ~r2_hidden(k4_tarski(sK0,sK0),sK2) | spl9_20),
% 1.57/0.58    inference(avatar_component_clause,[],[f371])).
% 1.57/0.58  fof(f371,plain,(
% 1.57/0.58    spl9_20 <=> r2_hidden(k4_tarski(sK0,sK0),sK2)),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 1.57/0.58  fof(f374,plain,(
% 1.57/0.58    ~spl9_20 | ~spl9_16),
% 1.57/0.58    inference(avatar_split_clause,[],[f363,f223,f371])).
% 1.57/0.58  fof(f363,plain,(
% 1.57/0.58    ~r2_hidden(k4_tarski(sK0,sK0),sK2) | ~spl9_16),
% 1.57/0.58    inference(forward_demodulation,[],[f362,f225])).
% 1.57/0.58  fof(f225,plain,(
% 1.57/0.58    sK0 = sK1 | ~spl9_16),
% 1.57/0.58    inference(avatar_component_clause,[],[f223])).
% 1.57/0.58  fof(f362,plain,(
% 1.57/0.58    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl9_16),
% 1.57/0.58    inference(subsumption_resolution,[],[f357,f72])).
% 1.57/0.58  fof(f72,plain,(
% 1.57/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.57/0.58    inference(equality_resolution,[],[f60])).
% 1.57/0.58  fof(f60,plain,(
% 1.57/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.57/0.58    inference(cnf_transformation,[],[f2])).
% 1.57/0.58  fof(f2,axiom,(
% 1.57/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.57/0.58  fof(f357,plain,(
% 1.57/0.58    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl9_16),
% 1.57/0.58    inference(backward_demodulation,[],[f29,f225])).
% 1.57/0.58  fof(f29,plain,(
% 1.57/0.58    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 1.57/0.58    inference(cnf_transformation,[],[f15])).
% 1.57/0.58  fof(f15,plain,(
% 1.57/0.58    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 1.57/0.58    inference(flattening,[],[f14])).
% 1.57/0.58  fof(f14,plain,(
% 1.57/0.58    ? [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 1.57/0.58    inference(ennf_transformation,[],[f13])).
% 1.57/0.58  fof(f13,negated_conjecture,(
% 1.57/0.58    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 1.57/0.58    inference(negated_conjecture,[],[f12])).
% 1.57/0.58  fof(f12,conjecture,(
% 1.57/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).
% 1.57/0.58  fof(f355,plain,(
% 1.57/0.58    ~spl9_1 | ~spl9_2 | spl9_7 | ~spl9_9),
% 1.57/0.58    inference(avatar_contradiction_clause,[],[f354])).
% 1.57/0.58  fof(f354,plain,(
% 1.57/0.58    $false | (~spl9_1 | ~spl9_2 | spl9_7 | ~spl9_9)),
% 1.57/0.58    inference(subsumption_resolution,[],[f352,f88])).
% 1.57/0.58  fof(f88,plain,(
% 1.57/0.58    ( ! [X8] : (r1_tarski(k3_relat_1(k2_wellord1(sK2,X8)),X8)) ) | ~spl9_1),
% 1.57/0.58    inference(resolution,[],[f76,f59])).
% 1.57/0.58  fof(f59,plain,(
% 1.57/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f22])).
% 1.57/0.58  fof(f22,plain,(
% 1.57/0.58    ! [X0,X1] : ((r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.57/0.58    inference(ennf_transformation,[],[f10])).
% 1.57/0.58  fof(f10,axiom,(
% 1.57/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_wellord1)).
% 1.57/0.58  fof(f352,plain,(
% 1.57/0.58    ~r1_tarski(k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))),k1_wellord1(sK2,sK1)) | (~spl9_1 | ~spl9_2 | spl9_7 | ~spl9_9)),
% 1.57/0.58    inference(resolution,[],[f294,f156])).
% 1.57/0.58  fof(f156,plain,(
% 1.57/0.58    r2_hidden(sK0,k1_wellord1(sK2,sK1)) | ~spl9_9),
% 1.57/0.58    inference(avatar_component_clause,[],[f155])).
% 1.57/0.58  fof(f155,plain,(
% 1.57/0.58    spl9_9 <=> r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 1.57/0.58  fof(f294,plain,(
% 1.57/0.58    ( ! [X2] : (~r2_hidden(sK0,k1_wellord1(sK2,X2)) | ~r1_tarski(k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X2))),k1_wellord1(sK2,sK1))) ) | (~spl9_1 | ~spl9_2 | spl9_7)),
% 1.57/0.58    inference(resolution,[],[f186,f247])).
% 1.57/0.58  fof(f247,plain,(
% 1.57/0.58    ( ! [X0] : (~r1_tarski(k1_wellord1(sK2,sK0),X0) | ~r1_tarski(X0,k1_wellord1(sK2,sK1))) ) | spl9_7),
% 1.57/0.58    inference(resolution,[],[f125,f67])).
% 1.57/0.58  fof(f67,plain,(
% 1.57/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f27])).
% 1.57/0.58  fof(f27,plain,(
% 1.57/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.57/0.58    inference(flattening,[],[f26])).
% 1.57/0.58  fof(f26,plain,(
% 1.57/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.57/0.58    inference(ennf_transformation,[],[f3])).
% 1.57/0.58  fof(f3,axiom,(
% 1.57/0.58    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.57/0.58  fof(f125,plain,(
% 1.57/0.58    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | spl9_7),
% 1.57/0.58    inference(avatar_component_clause,[],[f124])).
% 1.57/0.58  fof(f186,plain,(
% 1.57/0.58    ( ! [X0,X1] : (r1_tarski(k1_wellord1(sK2,X1),k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X0)))) | ~r2_hidden(X1,k1_wellord1(sK2,X0))) ) | (~spl9_1 | ~spl9_2)),
% 1.57/0.58    inference(subsumption_resolution,[],[f185,f87])).
% 1.57/0.58  fof(f87,plain,(
% 1.57/0.58    ( ! [X7] : (v1_relat_1(k2_wellord1(sK2,X7))) ) | ~spl9_1),
% 1.57/0.58    inference(resolution,[],[f76,f56])).
% 1.57/0.58  fof(f56,plain,(
% 1.57/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k2_wellord1(X0,X1))) )),
% 1.57/0.58    inference(cnf_transformation,[],[f20])).
% 1.57/0.58  fof(f20,plain,(
% 1.57/0.58    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 1.57/0.58    inference(ennf_transformation,[],[f6])).
% 1.57/0.58  fof(f6,axiom,(
% 1.57/0.58    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).
% 1.57/0.58  fof(f185,plain,(
% 1.57/0.58    ( ! [X0,X1] : (r1_tarski(k1_wellord1(sK2,X1),k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X0)))) | ~v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X0))) | ~r2_hidden(X1,k1_wellord1(sK2,X0))) ) | (~spl9_1 | ~spl9_2)),
% 1.57/0.58    inference(superposition,[],[f57,f93])).
% 1.57/0.58  fof(f93,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k1_wellord1(sK2,X0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),X0) | ~r2_hidden(X0,k1_wellord1(sK2,X1))) ) | (~spl9_1 | ~spl9_2)),
% 1.57/0.58    inference(subsumption_resolution,[],[f91,f76])).
% 1.57/0.58  fof(f91,plain,(
% 1.57/0.58    ( ! [X0,X1] : (~v1_relat_1(sK2) | ~r2_hidden(X0,k1_wellord1(sK2,X1)) | k1_wellord1(sK2,X0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),X0)) ) | ~spl9_2),
% 1.57/0.58    inference(resolution,[],[f81,f66])).
% 1.57/0.58  fof(f66,plain,(
% 1.57/0.58    ( ! [X2,X0,X1] : (~v2_wellord1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k1_wellord1(X2,X1)) | k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f25])).
% 1.57/0.58  fof(f25,plain,(
% 1.57/0.58    ! [X0,X1,X2] : (k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0) | ~r2_hidden(X0,k1_wellord1(X2,X1)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 1.57/0.58    inference(flattening,[],[f24])).
% 1.57/0.58  fof(f24,plain,(
% 1.57/0.58    ! [X0,X1,X2] : ((k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0) | (~r2_hidden(X0,k1_wellord1(X2,X1)) | ~v2_wellord1(X2))) | ~v1_relat_1(X2))),
% 1.57/0.58    inference(ennf_transformation,[],[f11])).
% 1.57/0.58  fof(f11,axiom,(
% 1.57/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X0,k1_wellord1(X2,X1)) & v2_wellord1(X2)) => k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0)))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_wellord1)).
% 1.57/0.58  fof(f81,plain,(
% 1.57/0.58    v2_wellord1(sK2) | ~spl9_2),
% 1.57/0.58    inference(avatar_component_clause,[],[f79])).
% 1.57/0.58  fof(f79,plain,(
% 1.57/0.58    spl9_2 <=> v2_wellord1(sK2)),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.57/0.58  fof(f57,plain,(
% 1.57/0.58    ( ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f21])).
% 1.57/0.58  fof(f21,plain,(
% 1.57/0.58    ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.57/0.58    inference(ennf_transformation,[],[f9])).
% 1.57/0.58  fof(f9,axiom,(
% 1.57/0.58    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).
% 1.57/0.58  fof(f254,plain,(
% 1.57/0.58    spl9_9 | ~spl9_1 | ~spl9_8),
% 1.57/0.58    inference(avatar_split_clause,[],[f251,f133,f74,f155])).
% 1.57/0.58  fof(f133,plain,(
% 1.57/0.58    spl9_8 <=> sP7(sK0,sK1,sK2)),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 1.57/0.58  fof(f251,plain,(
% 1.57/0.58    r2_hidden(sK0,k1_wellord1(sK2,sK1)) | (~spl9_1 | ~spl9_8)),
% 1.57/0.58    inference(resolution,[],[f134,f90])).
% 1.57/0.58  fof(f134,plain,(
% 1.57/0.58    sP7(sK0,sK1,sK2) | ~spl9_8),
% 1.57/0.58    inference(avatar_component_clause,[],[f133])).
% 1.57/0.58  fof(f250,plain,(
% 1.57/0.58    spl9_8 | spl9_16 | ~spl9_6),
% 1.57/0.58    inference(avatar_split_clause,[],[f232,f120,f223,f133])).
% 1.57/0.58  fof(f232,plain,(
% 1.57/0.58    sK0 = sK1 | sP7(sK0,sK1,sK2) | ~spl9_6),
% 1.57/0.58    inference(resolution,[],[f122,f49])).
% 1.57/0.58  fof(f122,plain,(
% 1.57/0.58    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl9_6),
% 1.57/0.58    inference(avatar_component_clause,[],[f120])).
% 1.57/0.58  fof(f203,plain,(
% 1.57/0.58    ~spl9_1 | ~spl9_2 | spl9_14),
% 1.57/0.58    inference(avatar_contradiction_clause,[],[f202])).
% 1.57/0.58  fof(f202,plain,(
% 1.57/0.58    $false | (~spl9_1 | ~spl9_2 | spl9_14)),
% 1.57/0.58    inference(subsumption_resolution,[],[f201,f81])).
% 1.57/0.58  fof(f201,plain,(
% 1.57/0.58    ~v2_wellord1(sK2) | (~spl9_1 | spl9_14)),
% 1.57/0.58    inference(subsumption_resolution,[],[f198,f76])).
% 1.57/0.58  fof(f198,plain,(
% 1.57/0.58    ~v1_relat_1(sK2) | ~v2_wellord1(sK2) | spl9_14),
% 1.57/0.58    inference(resolution,[],[f193,f46])).
% 1.57/0.58  fof(f46,plain,(
% 1.57/0.58    ( ! [X0] : (v6_relat_2(X0) | ~v1_relat_1(X0) | ~v2_wellord1(X0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f18])).
% 1.57/0.58  fof(f18,plain,(
% 1.57/0.58    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.57/0.58    inference(ennf_transformation,[],[f5])).
% 1.57/0.58  fof(f5,axiom,(
% 1.57/0.58    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).
% 1.57/0.58  fof(f193,plain,(
% 1.57/0.58    ~v6_relat_2(sK2) | spl9_14),
% 1.57/0.58    inference(avatar_component_clause,[],[f191])).
% 1.57/0.58  fof(f191,plain,(
% 1.57/0.58    spl9_14 <=> v6_relat_2(sK2)),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 1.57/0.58  fof(f197,plain,(
% 1.57/0.58    ~spl9_14 | spl9_15 | ~spl9_1),
% 1.57/0.58    inference(avatar_split_clause,[],[f84,f74,f195,f191])).
% 1.57/0.58  fof(f84,plain,(
% 1.57/0.58    ( ! [X2,X1] : (~r2_hidden(X1,k3_relat_1(sK2)) | ~r2_hidden(X2,k3_relat_1(sK2)) | X1 = X2 | r2_hidden(k4_tarski(X1,X2),sK2) | r2_hidden(k4_tarski(X2,X1),sK2) | ~v6_relat_2(sK2)) ) | ~spl9_1),
% 1.57/0.58    inference(resolution,[],[f76,f37])).
% 1.57/0.58  fof(f37,plain,(
% 1.57/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r2_hidden(X2,k3_relat_1(X0)) | X1 = X2 | r2_hidden(k4_tarski(X1,X2),X0) | r2_hidden(k4_tarski(X2,X1),X0) | ~v6_relat_2(X0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f17])).
% 1.57/0.58  fof(f17,plain,(
% 1.57/0.58    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 1.57/0.58    inference(ennf_transformation,[],[f8])).
% 1.57/0.58  fof(f8,axiom,(
% 1.57/0.58    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).
% 1.57/0.58  fof(f171,plain,(
% 1.57/0.58    ~spl9_1 | ~spl9_2 | spl9_10),
% 1.57/0.58    inference(avatar_contradiction_clause,[],[f170])).
% 1.57/0.58  fof(f170,plain,(
% 1.57/0.58    $false | (~spl9_1 | ~spl9_2 | spl9_10)),
% 1.57/0.58    inference(subsumption_resolution,[],[f169,f81])).
% 1.57/0.58  fof(f169,plain,(
% 1.57/0.58    ~v2_wellord1(sK2) | (~spl9_1 | spl9_10)),
% 1.57/0.58    inference(subsumption_resolution,[],[f167,f76])).
% 1.57/0.58  fof(f167,plain,(
% 1.57/0.58    ~v1_relat_1(sK2) | ~v2_wellord1(sK2) | spl9_10),
% 1.57/0.58    inference(resolution,[],[f162,f43])).
% 1.57/0.58  fof(f43,plain,(
% 1.57/0.58    ( ! [X0] : (v1_relat_2(X0) | ~v1_relat_1(X0) | ~v2_wellord1(X0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f18])).
% 1.57/0.58  fof(f162,plain,(
% 1.57/0.58    ~v1_relat_2(sK2) | spl9_10),
% 1.57/0.58    inference(avatar_component_clause,[],[f160])).
% 1.57/0.58  fof(f160,plain,(
% 1.57/0.58    spl9_10 <=> v1_relat_2(sK2)),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 1.57/0.58  fof(f166,plain,(
% 1.57/0.58    ~spl9_10 | spl9_11 | ~spl9_1),
% 1.57/0.58    inference(avatar_split_clause,[],[f83,f74,f164,f160])).
% 1.57/0.58  fof(f83,plain,(
% 1.57/0.58    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X0,X0),sK2) | ~v1_relat_2(sK2)) ) | ~spl9_1),
% 1.57/0.58    inference(resolution,[],[f76,f34])).
% 1.57/0.58  fof(f34,plain,(
% 1.57/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | r2_hidden(k4_tarski(X1,X1),X0) | ~v1_relat_2(X0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f16])).
% 1.57/0.58  fof(f16,plain,(
% 1.57/0.58    ! [X0] : ((v1_relat_2(X0) <=> ! [X1] : (r2_hidden(k4_tarski(X1,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 1.57/0.58    inference(ennf_transformation,[],[f7])).
% 1.57/0.58  fof(f7,axiom,(
% 1.57/0.58    ! [X0] : (v1_relat_1(X0) => (v1_relat_2(X0) <=> ! [X1] : (r2_hidden(X1,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X1),X0))))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).
% 1.57/0.58  fof(f129,plain,(
% 1.57/0.58    ~spl9_6 | ~spl9_7),
% 1.57/0.58    inference(avatar_split_clause,[],[f128,f124,f120])).
% 1.57/0.58  fof(f128,plain,(
% 1.57/0.58    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl9_7),
% 1.57/0.58    inference(subsumption_resolution,[],[f29,f126])).
% 1.57/0.58  fof(f127,plain,(
% 1.57/0.58    spl9_6 | spl9_7),
% 1.57/0.58    inference(avatar_split_clause,[],[f28,f124,f120])).
% 1.57/0.58  fof(f28,plain,(
% 1.57/0.58    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 1.57/0.58    inference(cnf_transformation,[],[f15])).
% 1.57/0.58  fof(f109,plain,(
% 1.57/0.58    spl9_5),
% 1.57/0.58    inference(avatar_split_clause,[],[f33,f106])).
% 1.57/0.58  fof(f33,plain,(
% 1.57/0.58    r2_hidden(sK1,k3_relat_1(sK2))),
% 1.57/0.58    inference(cnf_transformation,[],[f15])).
% 1.57/0.58  fof(f99,plain,(
% 1.57/0.58    spl9_3),
% 1.57/0.58    inference(avatar_split_clause,[],[f32,f96])).
% 1.57/0.58  fof(f32,plain,(
% 1.57/0.58    r2_hidden(sK0,k3_relat_1(sK2))),
% 1.57/0.58    inference(cnf_transformation,[],[f15])).
% 1.57/0.58  fof(f82,plain,(
% 1.57/0.58    spl9_2),
% 1.57/0.58    inference(avatar_split_clause,[],[f31,f79])).
% 1.57/0.58  fof(f31,plain,(
% 1.57/0.58    v2_wellord1(sK2)),
% 1.57/0.58    inference(cnf_transformation,[],[f15])).
% 1.57/0.58  fof(f77,plain,(
% 1.57/0.58    spl9_1),
% 1.57/0.58    inference(avatar_split_clause,[],[f30,f74])).
% 1.57/0.58  fof(f30,plain,(
% 1.57/0.58    v1_relat_1(sK2)),
% 1.57/0.58    inference(cnf_transformation,[],[f15])).
% 1.57/0.58  % SZS output end Proof for theBenchmark
% 1.57/0.58  % (7923)------------------------------
% 1.57/0.58  % (7923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (7923)Termination reason: Refutation
% 1.57/0.58  
% 1.57/0.58  % (7923)Memory used [KB]: 11129
% 1.57/0.58  % (7923)Time elapsed: 0.168 s
% 1.57/0.58  % (7923)------------------------------
% 1.57/0.58  % (7923)------------------------------
% 1.57/0.58  % (7902)Success in time 0.225 s
%------------------------------------------------------------------------------
