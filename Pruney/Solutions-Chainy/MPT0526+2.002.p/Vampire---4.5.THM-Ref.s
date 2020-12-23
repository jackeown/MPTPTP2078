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
% DateTime   : Thu Dec  3 12:48:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 162 expanded)
%              Number of leaves         :   24 (  77 expanded)
%              Depth                    :    6
%              Number of atoms          :  315 ( 514 expanded)
%              Number of equality atoms :   54 (  94 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f254,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f32,f36,f40,f44,f48,f52,f65,f69,f77,f92,f97,f114,f133,f153,f169,f188,f208,f234,f250])).

fof(f250,plain,
    ( ~ spl4_1
    | spl4_2
    | ~ spl4_5
    | ~ spl4_33 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | ~ spl4_1
    | spl4_2
    | ~ spl4_5
    | ~ spl4_33 ),
    inference(unit_resulting_resolution,[],[f27,f31,f233,f43])).

fof(f43,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | k8_relat_1(X0,X1) = X1 )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_5
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | k8_relat_1(X0,X1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f233,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl4_33
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f31,plain,
    ( sK0 != k8_relat_1(k2_relat_1(sK0),sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl4_2
  <=> sK0 = k8_relat_1(k2_relat_1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f27,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl4_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f234,plain,
    ( spl4_33
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f226,f206,f34,f26,f232])).

fof(f34,plain,
    ( spl4_3
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f206,plain,
    ( spl4_30
  <=> k2_relat_1(sK0) = k2_relat_1(k8_relat_1(k2_relat_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f226,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f219,f27])).

fof(f219,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl4_3
    | ~ spl4_30 ),
    inference(superposition,[],[f35,f207])).

fof(f207,plain,
    ( k2_relat_1(sK0) = k2_relat_1(k8_relat_1(k2_relat_1(sK0),sK0))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f206])).

fof(f35,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f208,plain,
    ( spl4_30
    | ~ spl4_23
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f198,f186,f151,f206])).

fof(f151,plain,
    ( spl4_23
  <=> ! [X1] :
        ( k2_relat_1(k8_relat_1(X1,sK0)) = X1
        | r2_hidden(sK1(k8_relat_1(X1,sK0),X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f186,plain,
    ( spl4_28
  <=> ! [X0] :
        ( k2_relat_1(k8_relat_1(X0,sK0)) = X0
        | ~ r2_hidden(sK1(k8_relat_1(X0,sK0),X0),k2_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f198,plain,
    ( k2_relat_1(sK0) = k2_relat_1(k8_relat_1(k2_relat_1(sK0),sK0))
    | ~ spl4_23
    | ~ spl4_28 ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,
    ( k2_relat_1(sK0) = k2_relat_1(k8_relat_1(k2_relat_1(sK0),sK0))
    | k2_relat_1(sK0) = k2_relat_1(k8_relat_1(k2_relat_1(sK0),sK0))
    | ~ spl4_23
    | ~ spl4_28 ),
    inference(resolution,[],[f187,f152])).

fof(f152,plain,
    ( ! [X1] :
        ( r2_hidden(sK1(k8_relat_1(X1,sK0),X1),X1)
        | k2_relat_1(k8_relat_1(X1,sK0)) = X1 )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f151])).

fof(f187,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1(k8_relat_1(X0,sK0),X0),k2_relat_1(sK0))
        | k2_relat_1(k8_relat_1(X0,sK0)) = X0 )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f186])).

fof(f188,plain,
    ( spl4_28
    | ~ spl4_1
    | ~ spl4_10
    | ~ spl4_23
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f180,f167,f151,f63,f26,f186])).

fof(f63,plain,
    ( spl4_10
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k2_relat_1(X2))
        | r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f167,plain,
    ( spl4_25
  <=> ! [X0] :
        ( k2_relat_1(k8_relat_1(X0,sK0)) = X0
        | ~ r2_hidden(sK1(k8_relat_1(X0,sK0),X0),k2_relat_1(k8_relat_1(X0,sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f180,plain,
    ( ! [X0] :
        ( k2_relat_1(k8_relat_1(X0,sK0)) = X0
        | ~ r2_hidden(sK1(k8_relat_1(X0,sK0),X0),k2_relat_1(sK0)) )
    | ~ spl4_1
    | ~ spl4_10
    | ~ spl4_23
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f179,f152])).

fof(f179,plain,
    ( ! [X0] :
        ( k2_relat_1(k8_relat_1(X0,sK0)) = X0
        | ~ r2_hidden(sK1(k8_relat_1(X0,sK0),X0),X0)
        | ~ r2_hidden(sK1(k8_relat_1(X0,sK0),X0),k2_relat_1(sK0)) )
    | ~ spl4_1
    | ~ spl4_10
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f175,f27])).

fof(f175,plain,
    ( ! [X0] :
        ( k2_relat_1(k8_relat_1(X0,sK0)) = X0
        | ~ r2_hidden(sK1(k8_relat_1(X0,sK0),X0),X0)
        | ~ r2_hidden(sK1(k8_relat_1(X0,sK0),X0),k2_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
    | ~ spl4_10
    | ~ spl4_25 ),
    inference(resolution,[],[f168,f64])).

fof(f64,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k2_relat_1(X2))
        | ~ v1_relat_1(X2) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f63])).

fof(f168,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1(k8_relat_1(X0,sK0),X0),k2_relat_1(k8_relat_1(X0,sK0)))
        | k2_relat_1(k8_relat_1(X0,sK0)) = X0 )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f167])).

fof(f169,plain,
    ( spl4_25
    | ~ spl4_7
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f142,f131,f50,f167])).

fof(f50,plain,
    ( spl4_7
  <=> ! [X0,X2] :
        ( r2_hidden(k4_tarski(sK2(X0,X2),X2),X0)
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f131,plain,
    ( spl4_20
  <=> ! [X3,X4] :
        ( k2_relat_1(k8_relat_1(X3,sK0)) = X3
        | ~ r2_hidden(k4_tarski(X4,sK1(k8_relat_1(X3,sK0),X3)),k8_relat_1(X3,sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f142,plain,
    ( ! [X0] :
        ( k2_relat_1(k8_relat_1(X0,sK0)) = X0
        | ~ r2_hidden(sK1(k8_relat_1(X0,sK0),X0),k2_relat_1(k8_relat_1(X0,sK0))) )
    | ~ spl4_7
    | ~ spl4_20 ),
    inference(resolution,[],[f132,f51])).

fof(f51,plain,
    ( ! [X2,X0] :
        ( r2_hidden(k4_tarski(sK2(X0,X2),X2),X0)
        | ~ r2_hidden(X2,k2_relat_1(X0)) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f132,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(k4_tarski(X4,sK1(k8_relat_1(X3,sK0),X3)),k8_relat_1(X3,sK0))
        | k2_relat_1(k8_relat_1(X3,sK0)) = X3 )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f131])).

fof(f153,plain,
    ( spl4_23
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f145,f131,f75,f151])).

fof(f75,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(sK3(X0,X1),sK1(X0,X1)),X0)
        | r2_hidden(sK1(X0,X1),X1)
        | k2_relat_1(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f145,plain,
    ( ! [X1] :
        ( k2_relat_1(k8_relat_1(X1,sK0)) = X1
        | r2_hidden(sK1(k8_relat_1(X1,sK0),X1),X1) )
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,
    ( ! [X1] :
        ( k2_relat_1(k8_relat_1(X1,sK0)) = X1
        | r2_hidden(sK1(k8_relat_1(X1,sK0),X1),X1)
        | k2_relat_1(k8_relat_1(X1,sK0)) = X1 )
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(resolution,[],[f132,f76])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK3(X0,X1),sK1(X0,X1)),X0)
        | r2_hidden(sK1(X0,X1),X1)
        | k2_relat_1(X0) = X1 )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f75])).

fof(f133,plain,
    ( spl4_20
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f124,f112,f75,f67,f131])).

fof(f67,plain,
    ( spl4_11
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
        | ~ r2_hidden(sK1(X0,X1),X1)
        | k2_relat_1(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f112,plain,
    ( spl4_18
  <=> ! [X9,X7,X8,X10] :
        ( ~ r2_hidden(k4_tarski(X7,sK1(X8,X9)),X8)
        | k2_relat_1(X8) = X9
        | ~ r2_hidden(k4_tarski(X10,sK1(X8,X9)),k8_relat_1(X9,sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f124,plain,
    ( ! [X4,X3] :
        ( k2_relat_1(k8_relat_1(X3,sK0)) = X3
        | ~ r2_hidden(k4_tarski(X4,sK1(k8_relat_1(X3,sK0),X3)),k8_relat_1(X3,sK0)) )
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f123,f68])).

fof(f68,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(sK1(X0,X1),X1)
        | ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
        | k2_relat_1(X0) = X1 )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f67])).

fof(f123,plain,
    ( ! [X4,X3] :
        ( k2_relat_1(k8_relat_1(X3,sK0)) = X3
        | ~ r2_hidden(k4_tarski(X4,sK1(k8_relat_1(X3,sK0),X3)),k8_relat_1(X3,sK0))
        | r2_hidden(sK1(k8_relat_1(X3,sK0),X3),X3) )
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,
    ( ! [X4,X3] :
        ( k2_relat_1(k8_relat_1(X3,sK0)) = X3
        | ~ r2_hidden(k4_tarski(X4,sK1(k8_relat_1(X3,sK0),X3)),k8_relat_1(X3,sK0))
        | r2_hidden(sK1(k8_relat_1(X3,sK0),X3),X3)
        | k2_relat_1(k8_relat_1(X3,sK0)) = X3 )
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(resolution,[],[f113,f76])).

fof(f113,plain,
    ( ! [X10,X8,X7,X9] :
        ( ~ r2_hidden(k4_tarski(X10,sK1(X8,X9)),k8_relat_1(X9,sK0))
        | k2_relat_1(X8) = X9
        | ~ r2_hidden(k4_tarski(X7,sK1(X8,X9)),X8) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f112])).

fof(f114,plain,
    ( spl4_18
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f105,f95,f38,f112])).

fof(f38,plain,
    ( spl4_4
  <=> ! [X3,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X3,X2),X0)
        | r2_hidden(X2,k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f95,plain,
    ( spl4_15
  <=> ! [X1,X0,X2] :
        ( k2_relat_1(X0) = X1
        | ~ r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0)
        | ~ r2_hidden(sK1(X0,X1),k2_relat_1(k8_relat_1(X1,sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f105,plain,
    ( ! [X10,X8,X7,X9] :
        ( ~ r2_hidden(k4_tarski(X7,sK1(X8,X9)),X8)
        | k2_relat_1(X8) = X9
        | ~ r2_hidden(k4_tarski(X10,sK1(X8,X9)),k8_relat_1(X9,sK0)) )
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(resolution,[],[f96,f39])).

fof(f39,plain,
    ( ! [X2,X0,X3] :
        ( r2_hidden(X2,k2_relat_1(X0))
        | ~ r2_hidden(k4_tarski(X3,X2),X0) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f96,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK1(X0,X1),k2_relat_1(k8_relat_1(X1,sK0)))
        | ~ r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0)
        | k2_relat_1(X0) = X1 )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f95])).

fof(f97,plain,
    ( spl4_15
    | ~ spl4_1
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f93,f90,f26,f95])).

fof(f90,plain,
    ( spl4_14
  <=> ! [X13,X15,X12,X14] :
        ( ~ r2_hidden(k4_tarski(X12,sK1(X13,X14)),X13)
        | k2_relat_1(X13) = X14
        | ~ v1_relat_1(X15)
        | ~ r2_hidden(sK1(X13,X14),k2_relat_1(k8_relat_1(X14,X15))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f93,plain,
    ( ! [X2,X0,X1] :
        ( k2_relat_1(X0) = X1
        | ~ r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0)
        | ~ r2_hidden(sK1(X0,X1),k2_relat_1(k8_relat_1(X1,sK0))) )
    | ~ spl4_1
    | ~ spl4_14 ),
    inference(resolution,[],[f91,f27])).

fof(f91,plain,
    ( ! [X14,X12,X15,X13] :
        ( ~ v1_relat_1(X15)
        | k2_relat_1(X13) = X14
        | ~ r2_hidden(k4_tarski(X12,sK1(X13,X14)),X13)
        | ~ r2_hidden(sK1(X13,X14),k2_relat_1(k8_relat_1(X14,X15))) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f90])).

fof(f92,plain,
    ( spl4_14
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f73,f67,f46,f90])).

fof(f46,plain,
    ( spl4_6
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f73,plain,
    ( ! [X14,X12,X15,X13] :
        ( ~ r2_hidden(k4_tarski(X12,sK1(X13,X14)),X13)
        | k2_relat_1(X13) = X14
        | ~ v1_relat_1(X15)
        | ~ r2_hidden(sK1(X13,X14),k2_relat_1(k8_relat_1(X14,X15))) )
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(resolution,[],[f68,f47])).

fof(f47,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,X1)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f77,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f18,f75])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK1(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f69,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f19,f67])).

fof(f19,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
      | ~ r2_hidden(sK1(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f65,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f22,f63])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_relat_1(X2))
      | r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_relat_1)).

fof(f52,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f23,f50])).

fof(f23,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK2(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f48,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f15,f42])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f40,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f24,f38])).

fof(f24,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f36,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f14,f34])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(f32,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f13,f30])).

fof(f13,plain,(
    sK0 != k8_relat_1(k2_relat_1(sK0),sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

fof(f28,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f12,f26])).

fof(f12,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (22886)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.48  % (22894)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.48  % (22886)Refutation not found, incomplete strategy% (22886)------------------------------
% 0.22/0.48  % (22886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (22886)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (22886)Memory used [KB]: 10618
% 0.22/0.49  % (22886)Time elapsed: 0.059 s
% 0.22/0.49  % (22886)------------------------------
% 0.22/0.49  % (22886)------------------------------
% 0.22/0.50  % (22875)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (22890)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (22878)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (22881)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (22877)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (22892)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (22876)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (22882)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (22876)Refutation not found, incomplete strategy% (22876)------------------------------
% 0.22/0.51  % (22876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22876)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22876)Memory used [KB]: 10490
% 0.22/0.51  % (22876)Time elapsed: 0.092 s
% 0.22/0.51  % (22876)------------------------------
% 0.22/0.51  % (22876)------------------------------
% 0.22/0.51  % (22884)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (22889)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (22893)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (22887)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (22880)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (22879)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.52  % (22895)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (22895)Refutation not found, incomplete strategy% (22895)------------------------------
% 0.22/0.52  % (22895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22895)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22895)Memory used [KB]: 10490
% 0.22/0.52  % (22895)Time elapsed: 0.108 s
% 0.22/0.52  % (22895)------------------------------
% 0.22/0.52  % (22895)------------------------------
% 0.22/0.52  % (22884)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f254,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f28,f32,f36,f40,f44,f48,f52,f65,f69,f77,f92,f97,f114,f133,f153,f169,f188,f208,f234,f250])).
% 0.22/0.52  fof(f250,plain,(
% 0.22/0.52    ~spl4_1 | spl4_2 | ~spl4_5 | ~spl4_33),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f247])).
% 0.22/0.52  fof(f247,plain,(
% 0.22/0.52    $false | (~spl4_1 | spl4_2 | ~spl4_5 | ~spl4_33)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f27,f31,f233,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1) ) | ~spl4_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    spl4_5 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.52  fof(f233,plain,(
% 0.22/0.52    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~spl4_33),
% 0.22/0.52    inference(avatar_component_clause,[],[f232])).
% 0.22/0.52  fof(f232,plain,(
% 0.22/0.52    spl4_33 <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    sK0 != k8_relat_1(k2_relat_1(sK0),sK0) | spl4_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    spl4_2 <=> sK0 = k8_relat_1(k2_relat_1(sK0),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    v1_relat_1(sK0) | ~spl4_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    spl4_1 <=> v1_relat_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.52  fof(f234,plain,(
% 0.22/0.52    spl4_33 | ~spl4_1 | ~spl4_3 | ~spl4_30),
% 0.22/0.52    inference(avatar_split_clause,[],[f226,f206,f34,f26,f232])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    spl4_3 <=> ! [X1,X0] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.52  fof(f206,plain,(
% 0.22/0.52    spl4_30 <=> k2_relat_1(sK0) = k2_relat_1(k8_relat_1(k2_relat_1(sK0),sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.22/0.52  fof(f226,plain,(
% 0.22/0.52    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | (~spl4_1 | ~spl4_3 | ~spl4_30)),
% 0.22/0.52    inference(subsumption_resolution,[],[f219,f27])).
% 0.22/0.52  fof(f219,plain,(
% 0.22/0.52    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl4_3 | ~spl4_30)),
% 0.22/0.52    inference(superposition,[],[f35,f207])).
% 0.22/0.52  fof(f207,plain,(
% 0.22/0.52    k2_relat_1(sK0) = k2_relat_1(k8_relat_1(k2_relat_1(sK0),sK0)) | ~spl4_30),
% 0.22/0.52    inference(avatar_component_clause,[],[f206])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) ) | ~spl4_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f34])).
% 0.22/0.52  fof(f208,plain,(
% 0.22/0.52    spl4_30 | ~spl4_23 | ~spl4_28),
% 0.22/0.52    inference(avatar_split_clause,[],[f198,f186,f151,f206])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    spl4_23 <=> ! [X1] : (k2_relat_1(k8_relat_1(X1,sK0)) = X1 | r2_hidden(sK1(k8_relat_1(X1,sK0),X1),X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.22/0.52  fof(f186,plain,(
% 0.22/0.52    spl4_28 <=> ! [X0] : (k2_relat_1(k8_relat_1(X0,sK0)) = X0 | ~r2_hidden(sK1(k8_relat_1(X0,sK0),X0),k2_relat_1(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.22/0.52  fof(f198,plain,(
% 0.22/0.52    k2_relat_1(sK0) = k2_relat_1(k8_relat_1(k2_relat_1(sK0),sK0)) | (~spl4_23 | ~spl4_28)),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f194])).
% 0.22/0.52  fof(f194,plain,(
% 0.22/0.52    k2_relat_1(sK0) = k2_relat_1(k8_relat_1(k2_relat_1(sK0),sK0)) | k2_relat_1(sK0) = k2_relat_1(k8_relat_1(k2_relat_1(sK0),sK0)) | (~spl4_23 | ~spl4_28)),
% 0.22/0.52    inference(resolution,[],[f187,f152])).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    ( ! [X1] : (r2_hidden(sK1(k8_relat_1(X1,sK0),X1),X1) | k2_relat_1(k8_relat_1(X1,sK0)) = X1) ) | ~spl4_23),
% 0.22/0.52    inference(avatar_component_clause,[],[f151])).
% 0.22/0.52  fof(f187,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(sK1(k8_relat_1(X0,sK0),X0),k2_relat_1(sK0)) | k2_relat_1(k8_relat_1(X0,sK0)) = X0) ) | ~spl4_28),
% 0.22/0.52    inference(avatar_component_clause,[],[f186])).
% 0.22/0.52  fof(f188,plain,(
% 0.22/0.52    spl4_28 | ~spl4_1 | ~spl4_10 | ~spl4_23 | ~spl4_25),
% 0.22/0.52    inference(avatar_split_clause,[],[f180,f167,f151,f63,f26,f186])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    spl4_10 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k2_relat_1(X2)) | r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.52  fof(f167,plain,(
% 0.22/0.52    spl4_25 <=> ! [X0] : (k2_relat_1(k8_relat_1(X0,sK0)) = X0 | ~r2_hidden(sK1(k8_relat_1(X0,sK0),X0),k2_relat_1(k8_relat_1(X0,sK0))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.22/0.52  fof(f180,plain,(
% 0.22/0.52    ( ! [X0] : (k2_relat_1(k8_relat_1(X0,sK0)) = X0 | ~r2_hidden(sK1(k8_relat_1(X0,sK0),X0),k2_relat_1(sK0))) ) | (~spl4_1 | ~spl4_10 | ~spl4_23 | ~spl4_25)),
% 0.22/0.52    inference(subsumption_resolution,[],[f179,f152])).
% 0.22/0.52  fof(f179,plain,(
% 0.22/0.52    ( ! [X0] : (k2_relat_1(k8_relat_1(X0,sK0)) = X0 | ~r2_hidden(sK1(k8_relat_1(X0,sK0),X0),X0) | ~r2_hidden(sK1(k8_relat_1(X0,sK0),X0),k2_relat_1(sK0))) ) | (~spl4_1 | ~spl4_10 | ~spl4_25)),
% 0.22/0.52    inference(subsumption_resolution,[],[f175,f27])).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    ( ! [X0] : (k2_relat_1(k8_relat_1(X0,sK0)) = X0 | ~r2_hidden(sK1(k8_relat_1(X0,sK0),X0),X0) | ~r2_hidden(sK1(k8_relat_1(X0,sK0),X0),k2_relat_1(sK0)) | ~v1_relat_1(sK0)) ) | (~spl4_10 | ~spl4_25)),
% 0.22/0.52    inference(resolution,[],[f168,f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k2_relat_1(X2)) | ~v1_relat_1(X2)) ) | ~spl4_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f63])).
% 0.22/0.52  fof(f168,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(sK1(k8_relat_1(X0,sK0),X0),k2_relat_1(k8_relat_1(X0,sK0))) | k2_relat_1(k8_relat_1(X0,sK0)) = X0) ) | ~spl4_25),
% 0.22/0.52    inference(avatar_component_clause,[],[f167])).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    spl4_25 | ~spl4_7 | ~spl4_20),
% 0.22/0.52    inference(avatar_split_clause,[],[f142,f131,f50,f167])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    spl4_7 <=> ! [X0,X2] : (r2_hidden(k4_tarski(sK2(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    spl4_20 <=> ! [X3,X4] : (k2_relat_1(k8_relat_1(X3,sK0)) = X3 | ~r2_hidden(k4_tarski(X4,sK1(k8_relat_1(X3,sK0),X3)),k8_relat_1(X3,sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    ( ! [X0] : (k2_relat_1(k8_relat_1(X0,sK0)) = X0 | ~r2_hidden(sK1(k8_relat_1(X0,sK0),X0),k2_relat_1(k8_relat_1(X0,sK0)))) ) | (~spl4_7 | ~spl4_20)),
% 0.22/0.52    inference(resolution,[],[f132,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK2(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) ) | ~spl4_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f50])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    ( ! [X4,X3] : (~r2_hidden(k4_tarski(X4,sK1(k8_relat_1(X3,sK0),X3)),k8_relat_1(X3,sK0)) | k2_relat_1(k8_relat_1(X3,sK0)) = X3) ) | ~spl4_20),
% 0.22/0.52    inference(avatar_component_clause,[],[f131])).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    spl4_23 | ~spl4_12 | ~spl4_20),
% 0.22/0.52    inference(avatar_split_clause,[],[f145,f131,f75,f151])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    spl4_12 <=> ! [X1,X0] : (r2_hidden(k4_tarski(sK3(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1) | k2_relat_1(X0) = X1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.52  fof(f145,plain,(
% 0.22/0.52    ( ! [X1] : (k2_relat_1(k8_relat_1(X1,sK0)) = X1 | r2_hidden(sK1(k8_relat_1(X1,sK0),X1),X1)) ) | (~spl4_12 | ~spl4_20)),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f143])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    ( ! [X1] : (k2_relat_1(k8_relat_1(X1,sK0)) = X1 | r2_hidden(sK1(k8_relat_1(X1,sK0),X1),X1) | k2_relat_1(k8_relat_1(X1,sK0)) = X1) ) | (~spl4_12 | ~spl4_20)),
% 0.22/0.52    inference(resolution,[],[f132,f76])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1) | k2_relat_1(X0) = X1) ) | ~spl4_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f75])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    spl4_20 | ~spl4_11 | ~spl4_12 | ~spl4_18),
% 0.22/0.52    inference(avatar_split_clause,[],[f124,f112,f75,f67,f131])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    spl4_11 <=> ! [X1,X3,X0] : (~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1) | k2_relat_1(X0) = X1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    spl4_18 <=> ! [X9,X7,X8,X10] : (~r2_hidden(k4_tarski(X7,sK1(X8,X9)),X8) | k2_relat_1(X8) = X9 | ~r2_hidden(k4_tarski(X10,sK1(X8,X9)),k8_relat_1(X9,sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    ( ! [X4,X3] : (k2_relat_1(k8_relat_1(X3,sK0)) = X3 | ~r2_hidden(k4_tarski(X4,sK1(k8_relat_1(X3,sK0),X3)),k8_relat_1(X3,sK0))) ) | (~spl4_11 | ~spl4_12 | ~spl4_18)),
% 0.22/0.52    inference(subsumption_resolution,[],[f123,f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | k2_relat_1(X0) = X1) ) | ~spl4_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f67])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    ( ! [X4,X3] : (k2_relat_1(k8_relat_1(X3,sK0)) = X3 | ~r2_hidden(k4_tarski(X4,sK1(k8_relat_1(X3,sK0),X3)),k8_relat_1(X3,sK0)) | r2_hidden(sK1(k8_relat_1(X3,sK0),X3),X3)) ) | (~spl4_12 | ~spl4_18)),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f121])).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    ( ! [X4,X3] : (k2_relat_1(k8_relat_1(X3,sK0)) = X3 | ~r2_hidden(k4_tarski(X4,sK1(k8_relat_1(X3,sK0),X3)),k8_relat_1(X3,sK0)) | r2_hidden(sK1(k8_relat_1(X3,sK0),X3),X3) | k2_relat_1(k8_relat_1(X3,sK0)) = X3) ) | (~spl4_12 | ~spl4_18)),
% 0.22/0.52    inference(resolution,[],[f113,f76])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    ( ! [X10,X8,X7,X9] : (~r2_hidden(k4_tarski(X10,sK1(X8,X9)),k8_relat_1(X9,sK0)) | k2_relat_1(X8) = X9 | ~r2_hidden(k4_tarski(X7,sK1(X8,X9)),X8)) ) | ~spl4_18),
% 0.22/0.52    inference(avatar_component_clause,[],[f112])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    spl4_18 | ~spl4_4 | ~spl4_15),
% 0.22/0.52    inference(avatar_split_clause,[],[f105,f95,f38,f112])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    spl4_4 <=> ! [X3,X0,X2] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    spl4_15 <=> ! [X1,X0,X2] : (k2_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),k2_relat_1(k8_relat_1(X1,sK0))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    ( ! [X10,X8,X7,X9] : (~r2_hidden(k4_tarski(X7,sK1(X8,X9)),X8) | k2_relat_1(X8) = X9 | ~r2_hidden(k4_tarski(X10,sK1(X8,X9)),k8_relat_1(X9,sK0))) ) | (~spl4_4 | ~spl4_15)),
% 0.22/0.52    inference(resolution,[],[f96,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X2,X0,X3] : (r2_hidden(X2,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X3,X2),X0)) ) | ~spl4_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f38])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK1(X0,X1),k2_relat_1(k8_relat_1(X1,sK0))) | ~r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) | k2_relat_1(X0) = X1) ) | ~spl4_15),
% 0.22/0.52    inference(avatar_component_clause,[],[f95])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    spl4_15 | ~spl4_1 | ~spl4_14),
% 0.22/0.52    inference(avatar_split_clause,[],[f93,f90,f26,f95])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    spl4_14 <=> ! [X13,X15,X12,X14] : (~r2_hidden(k4_tarski(X12,sK1(X13,X14)),X13) | k2_relat_1(X13) = X14 | ~v1_relat_1(X15) | ~r2_hidden(sK1(X13,X14),k2_relat_1(k8_relat_1(X14,X15))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),k2_relat_1(k8_relat_1(X1,sK0)))) ) | (~spl4_1 | ~spl4_14)),
% 0.22/0.52    inference(resolution,[],[f91,f27])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    ( ! [X14,X12,X15,X13] : (~v1_relat_1(X15) | k2_relat_1(X13) = X14 | ~r2_hidden(k4_tarski(X12,sK1(X13,X14)),X13) | ~r2_hidden(sK1(X13,X14),k2_relat_1(k8_relat_1(X14,X15)))) ) | ~spl4_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f90])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    spl4_14 | ~spl4_6 | ~spl4_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f73,f67,f46,f90])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    spl4_6 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ( ! [X14,X12,X15,X13] : (~r2_hidden(k4_tarski(X12,sK1(X13,X14)),X13) | k2_relat_1(X13) = X14 | ~v1_relat_1(X15) | ~r2_hidden(sK1(X13,X14),k2_relat_1(k8_relat_1(X14,X15)))) ) | (~spl4_6 | ~spl4_11)),
% 0.22/0.52    inference(resolution,[],[f68,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))) ) | ~spl4_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f46])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    spl4_12),
% 0.22/0.52    inference(avatar_split_clause,[],[f18,f75])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    spl4_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f19,f67])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    spl4_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f22,f63])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k2_relat_1(X2)) | r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_relat_1)).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    spl4_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f23,f50])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK2(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.22/0.52    inference(equality_resolution,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    spl4_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f20,f46])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    spl4_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f15,f42])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    spl4_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f24,f38])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.22/0.52    inference(equality_resolution,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    spl4_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f14,f34])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ~spl4_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f13,f30])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    sK0 != k8_relat_1(k2_relat_1(sK0),sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ? [X0] : (k8_relat_1(k2_relat_1(X0),X0) != X0 & v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,negated_conjecture,(
% 0.22/0.52    ~! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 0.22/0.52    inference(negated_conjecture,[],[f5])).
% 0.22/0.52  fof(f5,conjecture,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    spl4_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f12,f26])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    v1_relat_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (22884)------------------------------
% 0.22/0.52  % (22884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22884)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (22884)Memory used [KB]: 10746
% 0.22/0.52  % (22884)Time elapsed: 0.096 s
% 0.22/0.52  % (22884)------------------------------
% 0.22/0.52  % (22884)------------------------------
% 0.22/0.52  % (22874)Success in time 0.162 s
%------------------------------------------------------------------------------
