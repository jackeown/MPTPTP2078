%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 208 expanded)
%              Number of leaves         :   17 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  372 ( 744 expanded)
%              Number of equality atoms :   18 (  57 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f180,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f50,f66,f70,f78,f103,f110,f120,f122,f139,f150,f164,f169,f175,f176,f179])).

fof(f179,plain,
    ( spl6_17
    | ~ spl6_1
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f178,f108,f44,f162])).

fof(f162,plain,
    ( spl6_17
  <=> sP4(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f44,plain,
    ( spl6_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f108,plain,
    ( spl6_13
  <=> r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f178,plain,
    ( sP4(sK0,sK1,sK2)
    | ~ spl6_1
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f177,f45])).

fof(f45,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f177,plain,
    ( sP4(sK0,sK1,sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_13 ),
    inference(resolution,[],[f112,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_wellord1(X0,X1))
      | sP4(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(f112,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f108])).

fof(f176,plain,
    ( spl6_16
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f165,f162,f148])).

fof(f148,plain,
    ( spl6_16
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f165,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl6_17 ),
    inference(resolution,[],[f163,f23])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(k4_tarski(X3,X1),X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f163,plain,
    ( sP4(sK0,sK1,sK2)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f162])).

fof(f175,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | spl6_12
    | ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f106,f173])).

fof(f173,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f172,f45])).

fof(f172,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f171,f77])).

fof(f77,plain,
    ( r2_hidden(sK1,k3_relat_1(sK2))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl6_6
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f171,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK2))
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f170,f69])).

fof(f69,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl6_4
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f170,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl6_2
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f151,f49])).

fof(f49,plain,
    ( v2_wellord1(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl6_2
  <=> v2_wellord1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f151,plain,
    ( ~ v2_wellord1(sK2)
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl6_16 ),
    inference(resolution,[],[f149,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v2_wellord1(X2)
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

fof(f149,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f148])).

fof(f106,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl6_12
  <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f169,plain,
    ( ~ spl6_1
    | spl6_13
    | ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | ~ spl6_1
    | spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f167,f109])).

fof(f109,plain,
    ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | spl6_13 ),
    inference(avatar_component_clause,[],[f108])).

fof(f167,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl6_1
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f166,f45])).

fof(f166,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl6_17 ),
    inference(resolution,[],[f163,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f164,plain,
    ( spl6_17
    | spl6_11
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f153,f148,f101,f162])).

fof(f101,plain,
    ( spl6_11
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f153,plain,
    ( sP4(sK0,sK1,sK2)
    | spl6_11
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f152,f102])).

fof(f102,plain,
    ( sK0 != sK1
    | spl6_11 ),
    inference(avatar_component_clause,[],[f101])).

fof(f152,plain,
    ( sK0 = sK1
    | sP4(sK0,sK1,sK2)
    | ~ spl6_16 ),
    inference(resolution,[],[f149,f21])).

fof(f21,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X1),X0)
      | X1 = X3
      | sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f150,plain,
    ( spl6_16
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f131,f105,f76,f68,f48,f44,f148])).

fof(f131,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f130,f45])).

fof(f130,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f129,f77])).

fof(f129,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f128,f69])).

fof(f128,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f127,f49])).

fof(f127,plain,
    ( ~ v2_wellord1(sK2)
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl6_12 ),
    inference(resolution,[],[f121,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f121,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f105])).

fof(f139,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_10
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f137,f45])).

fof(f137,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl6_2
    | ~ spl6_4
    | spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f136,f99])).

fof(f99,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl6_10
  <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f136,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f135,f69])).

fof(f135,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f134,f49])).

fof(f134,plain,
    ( ~ v2_wellord1(sK2)
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl6_14 ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,
    ( ~ v2_wellord1(sK2)
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl6_14 ),
    inference(resolution,[],[f119,f29])).

fof(f119,plain,
    ( r2_hidden(k4_tarski(sK0,sK0),sK2)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl6_14
  <=> r2_hidden(k4_tarski(sK0,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f122,plain,
    ( spl6_12
    | spl6_11
    | spl6_13 ),
    inference(avatar_split_clause,[],[f115,f108,f101,f105])).

fof(f115,plain,
    ( sK0 = sK1
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | spl6_13 ),
    inference(subsumption_resolution,[],[f16,f109])).

fof(f16,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      <~> ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1 ) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      <~> ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1 ) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          <=> ( r2_hidden(X0,k1_wellord1(X2,X1))
              | X0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        <=> ( r2_hidden(X0,k1_wellord1(X2,X1))
            | X0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_wellord1)).

fof(f120,plain,
    ( spl6_14
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f85,f68,f64,f44,f118])).

fof(f64,plain,
    ( spl6_3
  <=> v1_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f85,plain,
    ( r2_hidden(k4_tarski(sK0,sK0),sK2)
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f84,f65])).

fof(f65,plain,
    ( v1_relat_2(sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f84,plain,
    ( r2_hidden(k4_tarski(sK0,sK0),sK2)
    | ~ v1_relat_2(sK2)
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f83,f45])).

fof(f83,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,sK0),sK2)
    | ~ v1_relat_2(sK2)
    | ~ spl6_4 ),
    inference(resolution,[],[f69,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X1,X1),X0)
      | ~ v1_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_wellord1)).

fof(f110,plain,
    ( ~ spl6_12
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f15,f108,f105])).

fof(f15,plain,
    ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f103,plain,
    ( ~ spl6_10
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f42,f101,f98])).

fof(f42,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) ),
    inference(inner_rewriting,[],[f14])).

fof(f14,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f78,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f20,f76])).

fof(f20,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f70,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f19,f68])).

fof(f19,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f66,plain,
    ( spl6_3
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f58,f48,f44,f64])).

fof(f58,plain,
    ( v1_relat_2(sK2)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f53,f45])).

fof(f53,plain,
    ( v1_relat_2(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_2 ),
    inference(resolution,[],[f49,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(f50,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f18,f48])).

fof(f18,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f46,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f17,f44])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (20166)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.46  % (20182)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.46  % (20173)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (20166)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f180,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f46,f50,f66,f70,f78,f103,f110,f120,f122,f139,f150,f164,f169,f175,f176,f179])).
% 0.20/0.47  fof(f179,plain,(
% 0.20/0.47    spl6_17 | ~spl6_1 | ~spl6_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f178,f108,f44,f162])).
% 0.20/0.47  fof(f162,plain,(
% 0.20/0.47    spl6_17 <=> sP4(sK0,sK1,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    spl6_1 <=> v1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    spl6_13 <=> r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    sP4(sK0,sK1,sK2) | (~spl6_1 | ~spl6_13)),
% 0.20/0.47    inference(subsumption_resolution,[],[f177,f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    v1_relat_1(sK2) | ~spl6_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f44])).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    sP4(sK0,sK1,sK2) | ~v1_relat_1(sK2) | ~spl6_13),
% 0.20/0.47    inference(resolution,[],[f112,f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_wellord1(X0,X1)) | sP4(X3,X1,X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | sP4(X3,X1,X0) | ~r2_hidden(X3,X2) | k1_wellord1(X0,X1) != X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    r2_hidden(sK0,k1_wellord1(sK2,sK1)) | ~spl6_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f108])).
% 0.20/0.47  fof(f176,plain,(
% 0.20/0.47    spl6_16 | ~spl6_17),
% 0.20/0.47    inference(avatar_split_clause,[],[f165,f162,f148])).
% 0.20/0.47  fof(f148,plain,(
% 0.20/0.47    spl6_16 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl6_17),
% 0.20/0.47    inference(resolution,[],[f163,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(k4_tarski(X3,X1),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    sP4(sK0,sK1,sK2) | ~spl6_17),
% 0.20/0.47    inference(avatar_component_clause,[],[f162])).
% 0.20/0.47  fof(f175,plain,(
% 0.20/0.47    ~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_6 | spl6_12 | ~spl6_16),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f174])).
% 0.20/0.47  fof(f174,plain,(
% 0.20/0.47    $false | (~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_6 | spl6_12 | ~spl6_16)),
% 0.20/0.47    inference(subsumption_resolution,[],[f106,f173])).
% 0.20/0.47  fof(f173,plain,(
% 0.20/0.47    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | (~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_6 | ~spl6_16)),
% 0.20/0.47    inference(subsumption_resolution,[],[f172,f45])).
% 0.20/0.47  fof(f172,plain,(
% 0.20/0.47    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~v1_relat_1(sK2) | (~spl6_2 | ~spl6_4 | ~spl6_6 | ~spl6_16)),
% 0.20/0.47    inference(subsumption_resolution,[],[f171,f77])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    r2_hidden(sK1,k3_relat_1(sK2)) | ~spl6_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f76])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    spl6_6 <=> r2_hidden(sK1,k3_relat_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.47  fof(f171,plain,(
% 0.20/0.47    ~r2_hidden(sK1,k3_relat_1(sK2)) | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~v1_relat_1(sK2) | (~spl6_2 | ~spl6_4 | ~spl6_16)),
% 0.20/0.47    inference(subsumption_resolution,[],[f170,f69])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    r2_hidden(sK0,k3_relat_1(sK2)) | ~spl6_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f68])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    spl6_4 <=> r2_hidden(sK0,k3_relat_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.47  fof(f170,plain,(
% 0.20/0.47    ~r2_hidden(sK0,k3_relat_1(sK2)) | ~r2_hidden(sK1,k3_relat_1(sK2)) | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~v1_relat_1(sK2) | (~spl6_2 | ~spl6_16)),
% 0.20/0.47    inference(subsumption_resolution,[],[f151,f49])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    v2_wellord1(sK2) | ~spl6_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    spl6_2 <=> v2_wellord1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.47  fof(f151,plain,(
% 0.20/0.47    ~v2_wellord1(sK2) | ~r2_hidden(sK0,k3_relat_1(sK2)) | ~r2_hidden(sK1,k3_relat_1(sK2)) | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~v1_relat_1(sK2) | ~spl6_16),
% 0.20/0.47    inference(resolution,[],[f149,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v2_wellord1(X2) | ~r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(X1,k3_relat_1(X2)) | r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(flattening,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) | (~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2))) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).
% 0.20/0.47  fof(f149,plain,(
% 0.20/0.47    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl6_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f148])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | spl6_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f105])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    spl6_12 <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.47  fof(f169,plain,(
% 0.20/0.47    ~spl6_1 | spl6_13 | ~spl6_17),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f168])).
% 0.20/0.47  fof(f168,plain,(
% 0.20/0.47    $false | (~spl6_1 | spl6_13 | ~spl6_17)),
% 0.20/0.47    inference(subsumption_resolution,[],[f167,f109])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    ~r2_hidden(sK0,k1_wellord1(sK2,sK1)) | spl6_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f108])).
% 0.20/0.47  fof(f167,plain,(
% 0.20/0.47    r2_hidden(sK0,k1_wellord1(sK2,sK1)) | (~spl6_1 | ~spl6_17)),
% 0.20/0.47    inference(subsumption_resolution,[],[f166,f45])).
% 0.20/0.47  fof(f166,plain,(
% 0.20/0.47    ~v1_relat_1(sK2) | r2_hidden(sK0,k1_wellord1(sK2,sK1)) | ~spl6_17),
% 0.20/0.47    inference(resolution,[],[f163,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | ~v1_relat_1(X0) | r2_hidden(X3,k1_wellord1(X0,X1))) )),
% 0.20/0.47    inference(equality_resolution,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~sP4(X3,X1,X0) | r2_hidden(X3,X2) | k1_wellord1(X0,X1) != X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    spl6_17 | spl6_11 | ~spl6_16),
% 0.20/0.47    inference(avatar_split_clause,[],[f153,f148,f101,f162])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    spl6_11 <=> sK0 = sK1),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.47  fof(f153,plain,(
% 0.20/0.47    sP4(sK0,sK1,sK2) | (spl6_11 | ~spl6_16)),
% 0.20/0.47    inference(subsumption_resolution,[],[f152,f102])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    sK0 != sK1 | spl6_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f101])).
% 0.20/0.47  fof(f152,plain,(
% 0.20/0.47    sK0 = sK1 | sP4(sK0,sK1,sK2) | ~spl6_16),
% 0.20/0.47    inference(resolution,[],[f149,f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | sP4(X3,X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f150,plain,(
% 0.20/0.47    spl6_16 | ~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_6 | ~spl6_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f131,f105,f76,f68,f48,f44,f148])).
% 0.20/0.47  fof(f131,plain,(
% 0.20/0.47    r2_hidden(k4_tarski(sK0,sK1),sK2) | (~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_6 | ~spl6_12)),
% 0.20/0.47    inference(subsumption_resolution,[],[f130,f45])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK0,sK1),sK2) | (~spl6_2 | ~spl6_4 | ~spl6_6 | ~spl6_12)),
% 0.20/0.47    inference(subsumption_resolution,[],[f129,f77])).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    ~r2_hidden(sK1,k3_relat_1(sK2)) | ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK0,sK1),sK2) | (~spl6_2 | ~spl6_4 | ~spl6_12)),
% 0.20/0.47    inference(subsumption_resolution,[],[f128,f69])).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    ~r2_hidden(sK0,k3_relat_1(sK2)) | ~r2_hidden(sK1,k3_relat_1(sK2)) | ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK0,sK1),sK2) | (~spl6_2 | ~spl6_12)),
% 0.20/0.47    inference(subsumption_resolution,[],[f127,f49])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    ~v2_wellord1(sK2) | ~r2_hidden(sK0,k3_relat_1(sK2)) | ~r2_hidden(sK1,k3_relat_1(sK2)) | ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl6_12),
% 0.20/0.47    inference(resolution,[],[f121,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~v2_wellord1(X2) | ~r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(X1,k3_relat_1(X2)) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl6_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f105])).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    ~spl6_1 | ~spl6_2 | ~spl6_4 | spl6_10 | ~spl6_14),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f138])).
% 0.20/0.47  fof(f138,plain,(
% 0.20/0.47    $false | (~spl6_1 | ~spl6_2 | ~spl6_4 | spl6_10 | ~spl6_14)),
% 0.20/0.47    inference(subsumption_resolution,[],[f137,f45])).
% 0.20/0.47  fof(f137,plain,(
% 0.20/0.47    ~v1_relat_1(sK2) | (~spl6_2 | ~spl6_4 | spl6_10 | ~spl6_14)),
% 0.20/0.47    inference(subsumption_resolution,[],[f136,f99])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | spl6_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f98])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    spl6_10 <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.47  fof(f136,plain,(
% 0.20/0.47    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | ~v1_relat_1(sK2) | (~spl6_2 | ~spl6_4 | ~spl6_14)),
% 0.20/0.47    inference(subsumption_resolution,[],[f135,f69])).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    ~r2_hidden(sK0,k3_relat_1(sK2)) | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | ~v1_relat_1(sK2) | (~spl6_2 | ~spl6_14)),
% 0.20/0.47    inference(subsumption_resolution,[],[f134,f49])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    ~v2_wellord1(sK2) | ~r2_hidden(sK0,k3_relat_1(sK2)) | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | ~v1_relat_1(sK2) | ~spl6_14),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f132])).
% 0.20/0.47  fof(f132,plain,(
% 0.20/0.47    ~v2_wellord1(sK2) | ~r2_hidden(sK0,k3_relat_1(sK2)) | ~r2_hidden(sK0,k3_relat_1(sK2)) | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | ~v1_relat_1(sK2) | ~spl6_14),
% 0.20/0.47    inference(resolution,[],[f119,f29])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    r2_hidden(k4_tarski(sK0,sK0),sK2) | ~spl6_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f118])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    spl6_14 <=> r2_hidden(k4_tarski(sK0,sK0),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    spl6_12 | spl6_11 | spl6_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f115,f108,f101,f105])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    sK0 = sK1 | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | spl6_13),
% 0.20/0.47    inference(subsumption_resolution,[],[f16,f109])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    sK0 = sK1 | r2_hidden(sK0,k1_wellord1(sK2,sK1)) | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ? [X0,X1,X2] : ((r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) <~> (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 0.20/0.47    inference(flattening,[],[f7])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (((r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) <~> (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1)) & (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) <=> (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1))))),
% 0.20/0.47    inference(negated_conjecture,[],[f5])).
% 0.20/0.47  fof(f5,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) <=> (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_wellord1)).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    spl6_14 | ~spl6_1 | ~spl6_3 | ~spl6_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f85,f68,f64,f44,f118])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl6_3 <=> v1_relat_2(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    r2_hidden(k4_tarski(sK0,sK0),sK2) | (~spl6_1 | ~spl6_3 | ~spl6_4)),
% 0.20/0.47    inference(subsumption_resolution,[],[f84,f65])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    v1_relat_2(sK2) | ~spl6_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f64])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    r2_hidden(k4_tarski(sK0,sK0),sK2) | ~v1_relat_2(sK2) | (~spl6_1 | ~spl6_4)),
% 0.20/0.47    inference(subsumption_resolution,[],[f83,f45])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK0,sK0),sK2) | ~v1_relat_2(sK2) | ~spl6_4),
% 0.20/0.47    inference(resolution,[],[f69,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X1,k3_relat_1(X0)) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(X1,X1),X0) | ~v1_relat_2(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0] : ((v1_relat_2(X0) <=> ! [X1] : (r2_hidden(k4_tarski(X1,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => (v1_relat_2(X0) <=> ! [X1] : (r2_hidden(X1,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X1),X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_wellord1)).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    ~spl6_12 | ~spl6_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f15,f108,f105])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ~r2_hidden(sK0,k1_wellord1(sK2,sK1)) | ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    ~spl6_10 | ~spl6_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f42,f101,f98])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    sK0 != sK1 | ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))),
% 0.20/0.47    inference(inner_rewriting,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    sK0 != sK1 | ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    spl6_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f20,f76])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    r2_hidden(sK1,k3_relat_1(sK2))),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    spl6_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f19,f68])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    r2_hidden(sK0,k3_relat_1(sK2))),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    spl6_3 | ~spl6_1 | ~spl6_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f58,f48,f44,f64])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    v1_relat_2(sK2) | (~spl6_1 | ~spl6_2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f53,f45])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    v1_relat_2(sK2) | ~v1_relat_1(sK2) | ~spl6_2),
% 0.20/0.47    inference(resolution,[],[f49,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X0] : (~v2_wellord1(X0) | v1_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    spl6_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f18,f48])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    v2_wellord1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    spl6_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f17,f44])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    v1_relat_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (20166)------------------------------
% 0.20/0.47  % (20166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (20166)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (20166)Memory used [KB]: 6268
% 0.20/0.47  % (20166)Time elapsed: 0.062 s
% 0.20/0.47  % (20166)------------------------------
% 0.20/0.47  % (20166)------------------------------
% 0.20/0.47  % (20157)Success in time 0.116 s
%------------------------------------------------------------------------------
