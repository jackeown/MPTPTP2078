%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 204 expanded)
%              Number of leaves         :   34 (  84 expanded)
%              Depth                    :    9
%              Number of atoms          :  419 ( 648 expanded)
%              Number of equality atoms :   85 ( 151 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f250,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f62,f64,f69,f78,f86,f90,f98,f103,f114,f118,f122,f127,f131,f135,f139,f144,f187,f196,f200,f205,f207,f220,f249])).

fof(f249,plain,
    ( ~ spl2_1
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_22
    | ~ spl2_26
    | ~ spl2_28 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_22
    | ~ spl2_26
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f209,f221])).

fof(f221,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))
    | ~ spl2_1
    | ~ spl2_12
    | ~ spl2_22
    | ~ spl2_28 ),
    inference(unit_resulting_resolution,[],[f52,f102,f167,f219])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k1_relat_1(X0),X1)
        | ~ r1_tarski(X1,k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | k1_xboole_0 = X1 )
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl2_28
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X1
        | ~ r1_tarski(X1,k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ r1_xboole_0(k1_relat_1(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f167,plain,
    ( r1_tarski(k1_tarski(sK0),k1_relat_1(sK1))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl2_22
  <=> r1_tarski(k1_tarski(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f102,plain,
    ( ! [X0] : k1_xboole_0 != k1_tarski(X0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl2_12
  <=> ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f52,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f209,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_26 ),
    inference(unit_resulting_resolution,[],[f52,f60,f195])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k11_relat_1(X0,X1)
        | r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl2_26
  <=> ! [X1,X0] :
        ( k1_xboole_0 != k11_relat_1(X0,X1)
        | r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f60,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_3
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f220,plain,
    ( spl2_28
    | ~ spl2_4
    | ~ spl2_20
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f163,f142,f137,f66,f218])).

fof(f66,plain,
    ( spl2_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f137,plain,
    ( spl2_20
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k7_relat_1(X1,X0)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f142,plain,
    ( spl2_21
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = X0
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X1
        | ~ r1_tarski(X1,k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ r1_xboole_0(k1_relat_1(X0),X1) )
    | ~ spl2_4
    | ~ spl2_20
    | ~ spl2_21 ),
    inference(forward_demodulation,[],[f162,f68])).

fof(f68,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k1_xboole_0) = X1
        | ~ r1_tarski(X1,k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ r1_xboole_0(k1_relat_1(X0),X1) )
    | ~ spl2_20
    | ~ spl2_21 ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k1_xboole_0) = X1
        | ~ r1_tarski(X1,k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ r1_xboole_0(k1_relat_1(X0),X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_20
    | ~ spl2_21 ),
    inference(superposition,[],[f143,f138])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k7_relat_1(X1,X0)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f137])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = X0
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f142])).

fof(f207,plain,
    ( ~ spl2_2
    | ~ spl2_11
    | spl2_22 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_11
    | spl2_22 ),
    inference(subsumption_resolution,[],[f171,f57])).

fof(f57,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl2_2
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f171,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl2_11
    | spl2_22 ),
    inference(resolution,[],[f168,f97])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f168,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k1_relat_1(sK1))
    | spl2_22 ),
    inference(avatar_component_clause,[],[f166])).

fof(f205,plain,
    ( ~ spl2_1
    | spl2_3
    | ~ spl2_17
    | ~ spl2_25
    | ~ spl2_27 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl2_1
    | spl2_3
    | ~ spl2_17
    | ~ spl2_25
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f188,f201])).

fof(f201,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))
    | ~ spl2_1
    | spl2_3
    | ~ spl2_27 ),
    inference(unit_resulting_resolution,[],[f52,f61,f199])).

fof(f199,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))
        | k1_xboole_0 = k11_relat_1(X0,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl2_27
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k11_relat_1(X0,X1)
        | ~ r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f61,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f188,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))
    | ~ spl2_1
    | ~ spl2_17
    | ~ spl2_25 ),
    inference(unit_resulting_resolution,[],[f52,f126,f186])).

fof(f186,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X1,k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | r1_xboole_0(k1_relat_1(X0),X1) )
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl2_25
  <=> ! [X1,X0] :
        ( r1_xboole_0(k1_relat_1(X0),X1)
        | ~ v1_relat_1(X0)
        | ~ r1_xboole_0(X1,k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f126,plain,
    ( r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl2_17
  <=> r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f200,plain,
    ( spl2_27
    | ~ spl2_14
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f152,f129,f112,f198])).

fof(f112,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f129,plain,
    ( spl2_18
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k9_relat_1(X1,X0)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k11_relat_1(X0,X1)
        | ~ r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_14
    | ~ spl2_18 ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k11_relat_1(X0,X1)
        | ~ r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_14
    | ~ spl2_18 ),
    inference(superposition,[],[f130,f113])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f112])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k9_relat_1(X1,X0)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f129])).

fof(f196,plain,
    ( spl2_26
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f146,f120,f112,f194])).

fof(f120,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k11_relat_1(X0,X1)
        | r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k11_relat_1(X0,X1)
        | r1_xboole_0(k1_relat_1(X0),k1_tarski(X1))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(superposition,[],[f121,f113])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k9_relat_1(X1,X0)
        | r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f120])).

fof(f187,plain,
    ( spl2_25
    | ~ spl2_15
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f156,f133,f116,f185])).

fof(f116,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k7_relat_1(X0,X1)
        | ~ r1_xboole_0(X1,k1_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f133,plain,
    ( spl2_19
  <=> ! [X1,X0] :
        ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k1_relat_1(X0),X1)
        | ~ v1_relat_1(X0)
        | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
    | ~ spl2_15
    | ~ spl2_19 ),
    inference(trivial_inequality_removal,[],[f155])).

fof(f155,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X0),X1)
        | ~ v1_relat_1(X0)
        | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
    | ~ spl2_15
    | ~ spl2_19 ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X0),X1)
        | ~ v1_relat_1(X0)
        | ~ r1_xboole_0(X1,k1_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl2_15
    | ~ spl2_19 ),
    inference(superposition,[],[f134,f117])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k7_relat_1(X0,X1)
        | ~ r1_xboole_0(X1,k1_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f116])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k7_relat_1(X1,X0)
        | r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f133])).

fof(f144,plain,(
    spl2_21 ),
    inference(avatar_split_clause,[],[f41,f142])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f139,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f45,f137])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f135,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f44,f133])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f131,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f43,f129])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f127,plain,
    ( spl2_17
    | spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f104,f88,f55,f124])).

fof(f88,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( r1_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f104,plain,
    ( r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1))
    | spl2_2
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f56,f89])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f88])).

fof(f56,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f122,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f42,f120])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f118,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f38,f116])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f114,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f37,f112])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f103,plain,
    ( spl2_12
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f99,f84,f76,f101])).

fof(f76,plain,
    ( spl2_6
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f84,plain,
    ( spl2_8
  <=> ! [X1,X0] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f99,plain,
    ( ! [X0] : k1_xboole_0 != k1_tarski(X0)
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(superposition,[],[f85,f77])).

fof(f77,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f85,plain,
    ( ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f84])).

fof(f98,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f48,f96])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f90,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f46,f88])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f86,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f39,f84])).

fof(f39,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f78,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f35,f76])).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f69,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f33,f66])).

fof(f33,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f64,plain,
    ( ~ spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f63,f59,f55])).

fof(f63,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl2_3 ),
    inference(subsumption_resolution,[],[f32,f61])).

fof(f32,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
      | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
      | r2_hidden(sK0,k1_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
        | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
      & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
        | r2_hidden(sK0,k1_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f62,plain,
    ( spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f31,f59,f55])).

fof(f31,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f30,f50])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:20:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (31875)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (31875)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f250,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f53,f62,f64,f69,f78,f86,f90,f98,f103,f114,f118,f122,f127,f131,f135,f139,f144,f187,f196,f200,f205,f207,f220,f249])).
% 0.21/0.46  fof(f249,plain,(
% 0.21/0.46    ~spl2_1 | ~spl2_3 | ~spl2_12 | ~spl2_22 | ~spl2_26 | ~spl2_28),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f248])).
% 0.21/0.46  fof(f248,plain,(
% 0.21/0.46    $false | (~spl2_1 | ~spl2_3 | ~spl2_12 | ~spl2_22 | ~spl2_26 | ~spl2_28)),
% 0.21/0.46    inference(subsumption_resolution,[],[f209,f221])).
% 0.21/0.46  fof(f221,plain,(
% 0.21/0.46    ~r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) | (~spl2_1 | ~spl2_12 | ~spl2_22 | ~spl2_28)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f52,f102,f167,f219])).
% 0.21/0.46  fof(f219,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X0),X1) | ~r1_tarski(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = X1) ) | ~spl2_28),
% 0.21/0.46    inference(avatar_component_clause,[],[f218])).
% 0.21/0.46  fof(f218,plain,(
% 0.21/0.46    spl2_28 <=> ! [X1,X0] : (k1_xboole_0 = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.21/0.46  fof(f167,plain,(
% 0.21/0.46    r1_tarski(k1_tarski(sK0),k1_relat_1(sK1)) | ~spl2_22),
% 0.21/0.46    inference(avatar_component_clause,[],[f166])).
% 0.21/0.46  fof(f166,plain,(
% 0.21/0.46    spl2_22 <=> r1_tarski(k1_tarski(sK0),k1_relat_1(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.46  fof(f102,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) ) | ~spl2_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f101])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    spl2_12 <=> ! [X0] : k1_xboole_0 != k1_tarski(X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.46  fof(f209,plain,(
% 0.21/0.46    r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) | (~spl2_1 | ~spl2_3 | ~spl2_26)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f52,f60,f195])).
% 0.21/0.46  fof(f195,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X0,X1) | r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) | ~v1_relat_1(X0)) ) | ~spl2_26),
% 0.21/0.46    inference(avatar_component_clause,[],[f194])).
% 0.21/0.46  fof(f194,plain,(
% 0.21/0.46    spl2_26 <=> ! [X1,X0] : (k1_xboole_0 != k11_relat_1(X0,X1) | r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl2_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f59])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    spl2_3 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.46  fof(f220,plain,(
% 0.21/0.46    spl2_28 | ~spl2_4 | ~spl2_20 | ~spl2_21),
% 0.21/0.46    inference(avatar_split_clause,[],[f163,f142,f137,f66,f218])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    spl2_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.46  fof(f137,plain,(
% 0.21/0.46    spl2_20 <=> ! [X1,X0] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.46  fof(f142,plain,(
% 0.21/0.46    spl2_21 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.46  fof(f163,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),X1)) ) | (~spl2_4 | ~spl2_20 | ~spl2_21)),
% 0.21/0.46    inference(forward_demodulation,[],[f162,f68])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl2_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f66])).
% 0.21/0.46  fof(f162,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),X1)) ) | (~spl2_20 | ~spl2_21)),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f159])).
% 0.21/0.46  fof(f159,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) ) | (~spl2_20 | ~spl2_21)),
% 0.21/0.46    inference(superposition,[],[f143,f138])).
% 0.21/0.46  fof(f138,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl2_20),
% 0.21/0.46    inference(avatar_component_clause,[],[f137])).
% 0.21/0.46  fof(f143,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl2_21),
% 0.21/0.46    inference(avatar_component_clause,[],[f142])).
% 0.21/0.46  fof(f207,plain,(
% 0.21/0.46    ~spl2_2 | ~spl2_11 | spl2_22),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f206])).
% 0.21/0.46  fof(f206,plain,(
% 0.21/0.46    $false | (~spl2_2 | ~spl2_11 | spl2_22)),
% 0.21/0.46    inference(subsumption_resolution,[],[f171,f57])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl2_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f55])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    spl2_2 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.46  fof(f171,plain,(
% 0.21/0.46    ~r2_hidden(sK0,k1_relat_1(sK1)) | (~spl2_11 | spl2_22)),
% 0.21/0.46    inference(resolution,[],[f168,f97])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) ) | ~spl2_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f96])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    spl2_11 <=> ! [X1,X0] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.46  fof(f168,plain,(
% 0.21/0.46    ~r1_tarski(k1_tarski(sK0),k1_relat_1(sK1)) | spl2_22),
% 0.21/0.46    inference(avatar_component_clause,[],[f166])).
% 0.21/0.46  fof(f205,plain,(
% 0.21/0.46    ~spl2_1 | spl2_3 | ~spl2_17 | ~spl2_25 | ~spl2_27),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f204])).
% 0.21/0.46  fof(f204,plain,(
% 0.21/0.46    $false | (~spl2_1 | spl2_3 | ~spl2_17 | ~spl2_25 | ~spl2_27)),
% 0.21/0.46    inference(subsumption_resolution,[],[f188,f201])).
% 0.21/0.46  fof(f201,plain,(
% 0.21/0.46    ~r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) | (~spl2_1 | spl2_3 | ~spl2_27)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f52,f61,f199])).
% 0.21/0.46  fof(f199,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) | k1_xboole_0 = k11_relat_1(X0,X1) | ~v1_relat_1(X0)) ) | ~spl2_27),
% 0.21/0.46    inference(avatar_component_clause,[],[f198])).
% 0.21/0.46  fof(f198,plain,(
% 0.21/0.46    spl2_27 <=> ! [X1,X0] : (k1_xboole_0 = k11_relat_1(X0,X1) | ~r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    k1_xboole_0 != k11_relat_1(sK1,sK0) | spl2_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f59])).
% 0.21/0.46  fof(f188,plain,(
% 0.21/0.46    r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) | (~spl2_1 | ~spl2_17 | ~spl2_25)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f52,f126,f186])).
% 0.21/0.46  fof(f186,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | r1_xboole_0(k1_relat_1(X0),X1)) ) | ~spl2_25),
% 0.21/0.46    inference(avatar_component_clause,[],[f185])).
% 0.21/0.46  fof(f185,plain,(
% 0.21/0.46    spl2_25 <=> ! [X1,X0] : (r1_xboole_0(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | ~r1_xboole_0(X1,k1_relat_1(X0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.46  fof(f126,plain,(
% 0.21/0.46    r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1)) | ~spl2_17),
% 0.21/0.46    inference(avatar_component_clause,[],[f124])).
% 0.21/0.46  fof(f124,plain,(
% 0.21/0.46    spl2_17 <=> r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.46  fof(f200,plain,(
% 0.21/0.46    spl2_27 | ~spl2_14 | ~spl2_18),
% 0.21/0.46    inference(avatar_split_clause,[],[f152,f129,f112,f198])).
% 0.21/0.46  fof(f112,plain,(
% 0.21/0.46    spl2_14 <=> ! [X1,X0] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.46  fof(f129,plain,(
% 0.21/0.46    spl2_18 <=> ! [X1,X0] : (k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.46  fof(f152,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 = k11_relat_1(X0,X1) | ~r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) | ~v1_relat_1(X0)) ) | (~spl2_14 | ~spl2_18)),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f147])).
% 0.21/0.46  fof(f147,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 = k11_relat_1(X0,X1) | ~r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) ) | (~spl2_14 | ~spl2_18)),
% 0.21/0.46    inference(superposition,[],[f130,f113])).
% 0.21/0.46  fof(f113,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) ) | ~spl2_14),
% 0.21/0.46    inference(avatar_component_clause,[],[f112])).
% 0.21/0.46  fof(f130,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl2_18),
% 0.21/0.46    inference(avatar_component_clause,[],[f129])).
% 0.21/0.46  fof(f196,plain,(
% 0.21/0.46    spl2_26 | ~spl2_14 | ~spl2_16),
% 0.21/0.46    inference(avatar_split_clause,[],[f146,f120,f112,f194])).
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    spl2_16 <=> ! [X1,X0] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.46  fof(f146,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X0,X1) | r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) | ~v1_relat_1(X0)) ) | (~spl2_14 | ~spl2_16)),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f145])).
% 0.21/0.46  fof(f145,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X0,X1) | r1_xboole_0(k1_relat_1(X0),k1_tarski(X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) ) | (~spl2_14 | ~spl2_16)),
% 0.21/0.46    inference(superposition,[],[f121,f113])).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl2_16),
% 0.21/0.46    inference(avatar_component_clause,[],[f120])).
% 0.21/0.46  fof(f187,plain,(
% 0.21/0.46    spl2_25 | ~spl2_15 | ~spl2_19),
% 0.21/0.46    inference(avatar_split_clause,[],[f156,f133,f116,f185])).
% 0.21/0.46  fof(f116,plain,(
% 0.21/0.46    spl2_15 <=> ! [X1,X0] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.46  fof(f133,plain,(
% 0.21/0.46    spl2_19 <=> ! [X1,X0] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.46  fof(f156,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | ~r1_xboole_0(X1,k1_relat_1(X0))) ) | (~spl2_15 | ~spl2_19)),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f155])).
% 0.21/0.46  fof(f155,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | ~r1_xboole_0(X1,k1_relat_1(X0))) ) | (~spl2_15 | ~spl2_19)),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f154])).
% 0.21/0.46  fof(f154,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) ) | (~spl2_15 | ~spl2_19)),
% 0.21/0.46    inference(superposition,[],[f134,f117])).
% 0.21/0.46  fof(f117,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl2_15),
% 0.21/0.46    inference(avatar_component_clause,[],[f116])).
% 0.21/0.46  fof(f134,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 != k7_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl2_19),
% 0.21/0.46    inference(avatar_component_clause,[],[f133])).
% 0.21/0.46  fof(f144,plain,(
% 0.21/0.46    spl2_21),
% 0.21/0.46    inference(avatar_split_clause,[],[f41,f142])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.46  fof(f139,plain,(
% 0.21/0.46    spl2_20),
% 0.21/0.46    inference(avatar_split_clause,[],[f45,f137])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(nnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.21/0.46  fof(f135,plain,(
% 0.21/0.46    spl2_19),
% 0.21/0.46    inference(avatar_split_clause,[],[f44,f133])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f28])).
% 0.21/0.46  fof(f131,plain,(
% 0.21/0.46    spl2_18),
% 0.21/0.46    inference(avatar_split_clause,[],[f43,f129])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(nnf_transformation,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.21/0.46  fof(f127,plain,(
% 0.21/0.46    spl2_17 | spl2_2 | ~spl2_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f104,f88,f55,f124])).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    spl2_9 <=> ! [X1,X0] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    r1_xboole_0(k1_tarski(sK0),k1_relat_1(sK1)) | (spl2_2 | ~spl2_9)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f56,f89])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) ) | ~spl2_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f88])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl2_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f55])).
% 0.21/0.46  fof(f122,plain,(
% 0.21/0.46    spl2_16),
% 0.21/0.46    inference(avatar_split_clause,[],[f42,f120])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    spl2_15),
% 0.21/0.46    inference(avatar_split_clause,[],[f38,f116])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 0.21/0.46  fof(f114,plain,(
% 0.21/0.46    spl2_14),
% 0.21/0.46    inference(avatar_split_clause,[],[f37,f112])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    spl2_12 | ~spl2_6 | ~spl2_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f99,f84,f76,f101])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    spl2_6 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    spl2_8 <=> ! [X1,X0] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) ) | (~spl2_6 | ~spl2_8)),
% 0.21/0.46    inference(superposition,[],[f85,f77])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f76])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) ) | ~spl2_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f84])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    spl2_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f48,f96])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.46    inference(nnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    spl2_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f46,f88])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    spl2_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f39,f84])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    spl2_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f35,f76])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    spl2_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f33,f66])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ~spl2_2 | spl2_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f63,f59,f55])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl2_3),
% 0.21/0.46    inference(subsumption_resolution,[],[f32,f61])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    (k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 0.21/0.46    inference(nnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.46    inference(negated_conjecture,[],[f13])).
% 0.21/0.46  fof(f13,conjecture,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    spl2_2 | ~spl2_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f31,f59,f55])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f26])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    spl2_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f30,f50])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    v1_relat_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f26])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (31875)------------------------------
% 0.21/0.46  % (31875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (31875)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (31875)Memory used [KB]: 6268
% 0.21/0.46  % (31875)Time elapsed: 0.012 s
% 0.21/0.46  % (31875)------------------------------
% 0.21/0.46  % (31875)------------------------------
% 0.21/0.47  % (31864)Success in time 0.106 s
%------------------------------------------------------------------------------
