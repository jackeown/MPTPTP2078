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
% DateTime   : Thu Dec  3 13:00:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 303 expanded)
%              Number of leaves         :   34 ( 119 expanded)
%              Depth                    :   13
%              Number of atoms          :  490 (1041 expanded)
%              Number of equality atoms :   90 ( 210 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f400,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f81,f86,f91,f108,f114,f119,f128,f133,f138,f147,f153,f184,f228,f243,f255,f266,f270,f321,f393,f396,f398,f399])).

fof(f399,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_relat_1(sK2)
    | r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ r2_hidden(sK4(sK2,sK1),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f398,plain,
    ( k1_xboole_0 != sK1
    | r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK4(sK2,sK1),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f396,plain,
    ( ~ spl8_1
    | ~ spl8_10
    | ~ spl8_11
    | spl8_12
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(avatar_contradiction_clause,[],[f395])).

fof(f395,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_10
    | ~ spl8_11
    | spl8_12
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f253,f394])).

fof(f394,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl8_1
    | ~ spl8_10
    | ~ spl8_11
    | spl8_12
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f271,f137])).

fof(f137,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl8_12 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl8_12
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f271,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl8_1
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_20 ),
    inference(resolution,[],[f249,f198])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK2,X0),k2_relat_1(sK2))
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK4(sK2,X0),X0) )
    | ~ spl8_1
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(resolution,[],[f185,f132])).

fof(f132,plain,
    ( ! [X1] :
        ( sP5(X1,sK2)
        | ~ r2_hidden(X1,k2_relat_1(sK2)) )
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl8_11
  <=> ! [X1] :
        ( sP5(X1,sK2)
        | ~ r2_hidden(X1,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f185,plain,
    ( ! [X3] :
        ( ~ sP5(sK4(sK2,X3),sK2)
        | ~ r2_hidden(sK4(sK2,X3),X3)
        | k2_relat_1(sK2) = X3 )
    | ~ spl8_1
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f76,f126])).

fof(f126,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl8_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f76,plain,
    ( ! [X3] :
        ( ~ v1_relat_1(sK2)
        | ~ sP5(sK4(sK2,X3),sK2)
        | ~ r2_hidden(sK4(sK2,X3),X3)
        | k2_relat_1(sK2) = X3 )
    | ~ spl8_1 ),
    inference(resolution,[],[f71,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ sP5(sK4(X0,X1),X0)
      | ~ r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f71,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl8_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f249,plain,
    ( r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl8_20
  <=> r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f253,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl8_21
  <=> r2_hidden(sK4(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f393,plain,
    ( ~ spl8_6
    | ~ spl8_10
    | ~ spl8_20
    | spl8_21 ),
    inference(avatar_contradiction_clause,[],[f392])).

fof(f392,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_20
    | spl8_21 ),
    inference(subsumption_resolution,[],[f391,f249])).

fof(f391,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ spl8_6
    | ~ spl8_10
    | spl8_21 ),
    inference(subsumption_resolution,[],[f389,f126])).

fof(f389,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ spl8_6
    | spl8_21 ),
    inference(resolution,[],[f291,f107])).

fof(f107,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl8_6
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f291,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(X0,sK1)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK4(sK2,sK1),k2_relat_1(X0)) )
    | spl8_21 ),
    inference(resolution,[],[f260,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f260,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r2_hidden(sK4(sK2,sK1),X0) )
    | spl8_21 ),
    inference(resolution,[],[f254,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f254,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | spl8_21 ),
    inference(avatar_component_clause,[],[f252])).

fof(f321,plain,
    ( spl8_25
    | ~ spl8_26
    | ~ spl8_1
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f289,f131,f125,f69,f318,f314])).

fof(f314,plain,
    ( spl8_25
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f318,plain,
    ( spl8_26
  <=> r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f289,plain,
    ( ~ r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl8_1
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f288,f185])).

fof(f288,plain,
    ( ~ r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK2)
    | sP5(sK4(sK2,k1_xboole_0),sK2)
    | ~ spl8_1
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(duplicate_literal_removal,[],[f286])).

fof(f286,plain,
    ( ~ r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK2)
    | sP5(sK4(sK2,k1_xboole_0),sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl8_1
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(resolution,[],[f256,f186])).

fof(f186,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK2,X2),X2)
        | sP5(sK4(sK2,X2),sK2)
        | k2_relat_1(sK2) = X2 )
    | ~ spl8_1
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f75,f126])).

fof(f75,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(sK2)
        | sP5(sK4(sK2,X2),sK2)
        | r2_hidden(sK4(sK2,X2),X2)
        | k2_relat_1(sK2) = X2 )
    | ~ spl8_1 ),
    inference(resolution,[],[f71,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP5(sK4(X0,X1),X0)
      | r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK2,X0),k1_xboole_0)
        | ~ r2_hidden(sK4(sK2,X0),X0)
        | k2_relat_1(sK2) = X0 )
    | ~ spl8_1
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(resolution,[],[f215,f34])).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f215,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(X5,k2_relat_1(sK2))
        | ~ r2_hidden(sK4(sK2,X4),X4)
        | ~ r2_hidden(sK4(sK2,X4),X5)
        | k2_relat_1(sK2) = X4 )
    | ~ spl8_1
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(resolution,[],[f198,f47])).

fof(f270,plain,
    ( spl8_20
    | ~ spl8_9
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f268,f225,f122,f247])).

fof(f122,plain,
    ( spl8_9
  <=> ! [X0] :
        ( ~ sP5(X0,sK2)
        | r2_hidden(X0,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f225,plain,
    ( spl8_18
  <=> sP5(sK4(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f268,plain,
    ( r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ spl8_9
    | ~ spl8_18 ),
    inference(resolution,[],[f227,f123])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ sP5(X0,sK2)
        | r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f227,plain,
    ( sP5(sK4(sK2,sK1),sK2)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f225])).

fof(f266,plain,
    ( spl8_18
    | ~ spl8_1
    | ~ spl8_10
    | spl8_12
    | spl8_21 ),
    inference(avatar_split_clause,[],[f261,f252,f135,f125,f69,f225])).

fof(f261,plain,
    ( sP5(sK4(sK2,sK1),sK2)
    | ~ spl8_1
    | ~ spl8_10
    | spl8_12
    | spl8_21 ),
    inference(subsumption_resolution,[],[f259,f137])).

fof(f259,plain,
    ( sP5(sK4(sK2,sK1),sK2)
    | sK1 = k2_relat_1(sK2)
    | ~ spl8_1
    | ~ spl8_10
    | spl8_21 ),
    inference(resolution,[],[f254,f186])).

fof(f255,plain,
    ( ~ spl8_21
    | spl8_19 ),
    inference(avatar_split_clause,[],[f244,f240,f252])).

fof(f240,plain,
    ( spl8_19
  <=> r2_hidden(sK3(sK4(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f244,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | spl8_19 ),
    inference(resolution,[],[f242,f28])).

fof(f28,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

fof(f242,plain,
    ( ~ r2_hidden(sK3(sK4(sK2,sK1)),sK0)
    | spl8_19 ),
    inference(avatar_component_clause,[],[f240])).

fof(f243,plain,
    ( spl8_18
    | ~ spl8_19
    | ~ spl8_15
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f235,f221,f150,f240,f225])).

fof(f150,plain,
    ( spl8_15
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f221,plain,
    ( spl8_17
  <=> sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f235,plain,
    ( ~ r2_hidden(sK3(sK4(sK2,sK1)),sK0)
    | sP5(sK4(sK2,sK1),sK2)
    | ~ spl8_15
    | ~ spl8_17 ),
    inference(forward_demodulation,[],[f231,f152])).

fof(f152,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f150])).

fof(f231,plain,
    ( sP5(sK4(sK2,sK1),sK2)
    | ~ r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2))
    | ~ spl8_17 ),
    inference(superposition,[],[f62,f223])).

fof(f223,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f221])).

fof(f62,plain,(
    ! [X0,X3] :
      ( sP5(k1_funct_1(X0,X3),X0)
      | ~ r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP5(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f228,plain,
    ( spl8_17
    | spl8_18
    | ~ spl8_1
    | ~ spl8_10
    | spl8_12 ),
    inference(avatar_split_clause,[],[f200,f135,f125,f69,f225,f221])).

fof(f200,plain,
    ( sP5(sK4(sK2,sK1),sK2)
    | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ spl8_1
    | ~ spl8_10
    | spl8_12 ),
    inference(subsumption_resolution,[],[f199,f137])).

fof(f199,plain,
    ( sP5(sK4(sK2,sK1),sK2)
    | sK1 = k2_relat_1(sK2)
    | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ spl8_1
    | ~ spl8_10 ),
    inference(resolution,[],[f186,f29])).

fof(f29,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f184,plain,
    ( ~ spl8_3
    | spl8_10 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | ~ spl8_3
    | spl8_10 ),
    inference(subsumption_resolution,[],[f182,f43])).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f182,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl8_3
    | spl8_10 ),
    inference(resolution,[],[f129,f85])).

fof(f85,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl8_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl8_10 ),
    inference(resolution,[],[f127,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f127,plain,
    ( ~ v1_relat_1(sK2)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f125])).

fof(f153,plain,
    ( spl8_15
    | ~ spl8_8
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f148,f140,f116,f150])).

fof(f116,plain,
    ( spl8_8
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f140,plain,
    ( spl8_13
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f148,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_8
    | ~ spl8_13 ),
    inference(backward_demodulation,[],[f118,f142])).

fof(f142,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f140])).

fof(f118,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f147,plain,
    ( spl8_13
    | spl8_14
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f98,f83,f78,f144,f140])).

fof(f144,plain,
    ( spl8_14
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f78,plain,
    ( spl8_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f98,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f93,f80])).

fof(f80,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f93,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl8_3 ),
    inference(resolution,[],[f85,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f138,plain,
    ( ~ spl8_12
    | spl8_4
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f120,f111,f88,f135])).

fof(f88,plain,
    ( spl8_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f111,plain,
    ( spl8_7
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f120,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl8_4
    | ~ spl8_7 ),
    inference(superposition,[],[f90,f113])).

fof(f113,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f90,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f133,plain,
    ( spl8_11
    | ~ spl8_10
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f74,f69,f125,f131])).

fof(f74,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK2)
        | sP5(X1,sK2)
        | ~ r2_hidden(X1,k2_relat_1(sK2)) )
    | ~ spl8_1 ),
    inference(resolution,[],[f71,f60])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP5(X2,X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP5(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f128,plain,
    ( spl8_9
    | ~ spl8_10
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f73,f69,f125,f122])).

fof(f73,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ sP5(X0,sK2)
        | r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl8_1 ),
    inference(resolution,[],[f71,f61])).

fof(f61,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ sP5(X2,X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP5(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f119,plain,
    ( spl8_8
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f97,f83,f116])).

fof(f97,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl8_3 ),
    inference(resolution,[],[f85,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f114,plain,
    ( spl8_7
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f96,f83,f111])).

fof(f96,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl8_3 ),
    inference(resolution,[],[f85,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f108,plain,
    ( spl8_6
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f95,f83,f105])).

fof(f95,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl8_3 ),
    inference(resolution,[],[f85,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f91,plain,(
    ~ spl8_4 ),
    inference(avatar_split_clause,[],[f33,f88])).

fof(f33,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f86,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f32,f83])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f81,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f31,f78])).

fof(f31,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f72,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f30,f69])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n009.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 19:45:41 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.20/0.44  % (11219)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.46  % (11213)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.47  % (11235)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.48  % (11227)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.49  % (11210)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.50  % (11217)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (11211)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (11225)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (11209)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (11227)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f400,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f72,f81,f86,f91,f108,f114,f119,f128,f133,f138,f147,f153,f184,f228,f243,f255,f266,f270,f321,f393,f396,f398,f399])).
% 0.20/0.51  fof(f399,plain,(
% 0.20/0.51    k1_xboole_0 != sK1 | k1_xboole_0 != k2_relat_1(sK2) | r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) | ~r2_hidden(sK4(sK2,sK1),sK1)),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f398,plain,(
% 0.20/0.51    k1_xboole_0 != sK1 | r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0) | ~r2_hidden(sK4(sK2,sK1),sK1)),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f396,plain,(
% 0.20/0.51    ~spl8_1 | ~spl8_10 | ~spl8_11 | spl8_12 | ~spl8_20 | ~spl8_21),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f395])).
% 0.20/0.51  fof(f395,plain,(
% 0.20/0.51    $false | (~spl8_1 | ~spl8_10 | ~spl8_11 | spl8_12 | ~spl8_20 | ~spl8_21)),
% 0.20/0.51    inference(subsumption_resolution,[],[f253,f394])).
% 0.20/0.51  fof(f394,plain,(
% 0.20/0.51    ~r2_hidden(sK4(sK2,sK1),sK1) | (~spl8_1 | ~spl8_10 | ~spl8_11 | spl8_12 | ~spl8_20)),
% 0.20/0.51    inference(subsumption_resolution,[],[f271,f137])).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    sK1 != k2_relat_1(sK2) | spl8_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f135])).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    spl8_12 <=> sK1 = k2_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.20/0.51  fof(f271,plain,(
% 0.20/0.51    sK1 = k2_relat_1(sK2) | ~r2_hidden(sK4(sK2,sK1),sK1) | (~spl8_1 | ~spl8_10 | ~spl8_11 | ~spl8_20)),
% 0.20/0.51    inference(resolution,[],[f249,f198])).
% 0.20/0.51  fof(f198,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(sK4(sK2,X0),k2_relat_1(sK2)) | k2_relat_1(sK2) = X0 | ~r2_hidden(sK4(sK2,X0),X0)) ) | (~spl8_1 | ~spl8_10 | ~spl8_11)),
% 0.20/0.51    inference(resolution,[],[f185,f132])).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    ( ! [X1] : (sP5(X1,sK2) | ~r2_hidden(X1,k2_relat_1(sK2))) ) | ~spl8_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f131])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    spl8_11 <=> ! [X1] : (sP5(X1,sK2) | ~r2_hidden(X1,k2_relat_1(sK2)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.20/0.51  fof(f185,plain,(
% 0.20/0.51    ( ! [X3] : (~sP5(sK4(sK2,X3),sK2) | ~r2_hidden(sK4(sK2,X3),X3) | k2_relat_1(sK2) = X3) ) | (~spl8_1 | ~spl8_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f76,f126])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    v1_relat_1(sK2) | ~spl8_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f125])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    spl8_10 <=> v1_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ( ! [X3] : (~v1_relat_1(sK2) | ~sP5(sK4(sK2,X3),sK2) | ~r2_hidden(sK4(sK2,X3),X3) | k2_relat_1(sK2) = X3) ) | ~spl8_1),
% 0.20/0.51    inference(resolution,[],[f71,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~sP5(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    v1_funct_1(sK2) | ~spl8_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f69])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    spl8_1 <=> v1_funct_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.51  fof(f249,plain,(
% 0.20/0.51    r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) | ~spl8_20),
% 0.20/0.51    inference(avatar_component_clause,[],[f247])).
% 0.20/0.51  fof(f247,plain,(
% 0.20/0.51    spl8_20 <=> r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.20/0.51  fof(f253,plain,(
% 0.20/0.51    r2_hidden(sK4(sK2,sK1),sK1) | ~spl8_21),
% 0.20/0.51    inference(avatar_component_clause,[],[f252])).
% 0.20/0.51  fof(f252,plain,(
% 0.20/0.51    spl8_21 <=> r2_hidden(sK4(sK2,sK1),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.20/0.51  fof(f393,plain,(
% 0.20/0.51    ~spl8_6 | ~spl8_10 | ~spl8_20 | spl8_21),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f392])).
% 0.20/0.51  fof(f392,plain,(
% 0.20/0.51    $false | (~spl8_6 | ~spl8_10 | ~spl8_20 | spl8_21)),
% 0.20/0.51    inference(subsumption_resolution,[],[f391,f249])).
% 0.20/0.51  fof(f391,plain,(
% 0.20/0.51    ~r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) | (~spl8_6 | ~spl8_10 | spl8_21)),
% 0.20/0.51    inference(subsumption_resolution,[],[f389,f126])).
% 0.20/0.51  fof(f389,plain,(
% 0.20/0.51    ~v1_relat_1(sK2) | ~r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) | (~spl8_6 | spl8_21)),
% 0.20/0.51    inference(resolution,[],[f291,f107])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    v5_relat_1(sK2,sK1) | ~spl8_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f105])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    spl8_6 <=> v5_relat_1(sK2,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.51  fof(f291,plain,(
% 0.20/0.51    ( ! [X0] : (~v5_relat_1(X0,sK1) | ~v1_relat_1(X0) | ~r2_hidden(sK4(sK2,sK1),k2_relat_1(X0))) ) | spl8_21),
% 0.20/0.51    inference(resolution,[],[f260,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.51  fof(f260,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r2_hidden(sK4(sK2,sK1),X0)) ) | spl8_21),
% 0.20/0.51    inference(resolution,[],[f254,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.51  fof(f254,plain,(
% 0.20/0.51    ~r2_hidden(sK4(sK2,sK1),sK1) | spl8_21),
% 0.20/0.51    inference(avatar_component_clause,[],[f252])).
% 0.20/0.51  fof(f321,plain,(
% 0.20/0.51    spl8_25 | ~spl8_26 | ~spl8_1 | ~spl8_10 | ~spl8_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f289,f131,f125,f69,f318,f314])).
% 0.20/0.51  fof(f314,plain,(
% 0.20/0.51    spl8_25 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.20/0.51  fof(f318,plain,(
% 0.20/0.51    spl8_26 <=> r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.20/0.51  fof(f289,plain,(
% 0.20/0.51    ~r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK2) | (~spl8_1 | ~spl8_10 | ~spl8_11)),
% 0.20/0.51    inference(subsumption_resolution,[],[f288,f185])).
% 0.20/0.51  fof(f288,plain,(
% 0.20/0.51    ~r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK2) | sP5(sK4(sK2,k1_xboole_0),sK2) | (~spl8_1 | ~spl8_10 | ~spl8_11)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f286])).
% 0.20/0.51  fof(f286,plain,(
% 0.20/0.51    ~r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK2) | sP5(sK4(sK2,k1_xboole_0),sK2) | k1_xboole_0 = k2_relat_1(sK2) | (~spl8_1 | ~spl8_10 | ~spl8_11)),
% 0.20/0.51    inference(resolution,[],[f256,f186])).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    ( ! [X2] : (r2_hidden(sK4(sK2,X2),X2) | sP5(sK4(sK2,X2),sK2) | k2_relat_1(sK2) = X2) ) | (~spl8_1 | ~spl8_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f75,f126])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    ( ! [X2] : (~v1_relat_1(sK2) | sP5(sK4(sK2,X2),sK2) | r2_hidden(sK4(sK2,X2),X2) | k2_relat_1(sK2) = X2) ) | ~spl8_1),
% 0.20/0.51    inference(resolution,[],[f71,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | sP5(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f256,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(sK4(sK2,X0),k1_xboole_0) | ~r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0) ) | (~spl8_1 | ~spl8_10 | ~spl8_11)),
% 0.20/0.51    inference(resolution,[],[f215,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.51  fof(f215,plain,(
% 0.20/0.51    ( ! [X4,X5] : (~r1_tarski(X5,k2_relat_1(sK2)) | ~r2_hidden(sK4(sK2,X4),X4) | ~r2_hidden(sK4(sK2,X4),X5) | k2_relat_1(sK2) = X4) ) | (~spl8_1 | ~spl8_10 | ~spl8_11)),
% 0.20/0.51    inference(resolution,[],[f198,f47])).
% 0.20/0.51  fof(f270,plain,(
% 0.20/0.51    spl8_20 | ~spl8_9 | ~spl8_18),
% 0.20/0.51    inference(avatar_split_clause,[],[f268,f225,f122,f247])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    spl8_9 <=> ! [X0] : (~sP5(X0,sK2) | r2_hidden(X0,k2_relat_1(sK2)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.51  fof(f225,plain,(
% 0.20/0.51    spl8_18 <=> sP5(sK4(sK2,sK1),sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.20/0.51  fof(f268,plain,(
% 0.20/0.51    r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) | (~spl8_9 | ~spl8_18)),
% 0.20/0.51    inference(resolution,[],[f227,f123])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    ( ! [X0] : (~sP5(X0,sK2) | r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl8_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f122])).
% 0.20/0.51  fof(f227,plain,(
% 0.20/0.51    sP5(sK4(sK2,sK1),sK2) | ~spl8_18),
% 0.20/0.51    inference(avatar_component_clause,[],[f225])).
% 0.20/0.51  fof(f266,plain,(
% 0.20/0.51    spl8_18 | ~spl8_1 | ~spl8_10 | spl8_12 | spl8_21),
% 0.20/0.51    inference(avatar_split_clause,[],[f261,f252,f135,f125,f69,f225])).
% 0.20/0.51  fof(f261,plain,(
% 0.20/0.51    sP5(sK4(sK2,sK1),sK2) | (~spl8_1 | ~spl8_10 | spl8_12 | spl8_21)),
% 0.20/0.51    inference(subsumption_resolution,[],[f259,f137])).
% 0.20/0.51  fof(f259,plain,(
% 0.20/0.51    sP5(sK4(sK2,sK1),sK2) | sK1 = k2_relat_1(sK2) | (~spl8_1 | ~spl8_10 | spl8_21)),
% 0.20/0.51    inference(resolution,[],[f254,f186])).
% 0.20/0.51  fof(f255,plain,(
% 0.20/0.51    ~spl8_21 | spl8_19),
% 0.20/0.51    inference(avatar_split_clause,[],[f244,f240,f252])).
% 0.20/0.51  fof(f240,plain,(
% 0.20/0.51    spl8_19 <=> r2_hidden(sK3(sK4(sK2,sK1)),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.20/0.51  fof(f244,plain,(
% 0.20/0.51    ~r2_hidden(sK4(sK2,sK1),sK1) | spl8_19),
% 0.20/0.51    inference(resolution,[],[f242,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.51    inference(flattening,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.20/0.51    inference(negated_conjecture,[],[f12])).
% 0.20/0.51  fof(f12,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 0.20/0.51  fof(f242,plain,(
% 0.20/0.51    ~r2_hidden(sK3(sK4(sK2,sK1)),sK0) | spl8_19),
% 0.20/0.51    inference(avatar_component_clause,[],[f240])).
% 0.20/0.51  fof(f243,plain,(
% 0.20/0.51    spl8_18 | ~spl8_19 | ~spl8_15 | ~spl8_17),
% 0.20/0.51    inference(avatar_split_clause,[],[f235,f221,f150,f240,f225])).
% 0.20/0.51  fof(f150,plain,(
% 0.20/0.51    spl8_15 <=> sK0 = k1_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.20/0.51  fof(f221,plain,(
% 0.20/0.51    spl8_17 <=> sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.20/0.51  fof(f235,plain,(
% 0.20/0.51    ~r2_hidden(sK3(sK4(sK2,sK1)),sK0) | sP5(sK4(sK2,sK1),sK2) | (~spl8_15 | ~spl8_17)),
% 0.20/0.51    inference(forward_demodulation,[],[f231,f152])).
% 0.20/0.51  fof(f152,plain,(
% 0.20/0.51    sK0 = k1_relat_1(sK2) | ~spl8_15),
% 0.20/0.51    inference(avatar_component_clause,[],[f150])).
% 0.20/0.51  fof(f231,plain,(
% 0.20/0.51    sP5(sK4(sK2,sK1),sK2) | ~r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2)) | ~spl8_17),
% 0.20/0.51    inference(superposition,[],[f62,f223])).
% 0.20/0.51  fof(f223,plain,(
% 0.20/0.51    sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | ~spl8_17),
% 0.20/0.51    inference(avatar_component_clause,[],[f221])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0,X3] : (sP5(k1_funct_1(X0,X3),X0) | ~r2_hidden(X3,k1_relat_1(X0))) )),
% 0.20/0.51    inference(equality_resolution,[],[f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X2,X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | sP5(X2,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f228,plain,(
% 0.20/0.51    spl8_17 | spl8_18 | ~spl8_1 | ~spl8_10 | spl8_12),
% 0.20/0.51    inference(avatar_split_clause,[],[f200,f135,f125,f69,f225,f221])).
% 0.20/0.51  fof(f200,plain,(
% 0.20/0.51    sP5(sK4(sK2,sK1),sK2) | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | (~spl8_1 | ~spl8_10 | spl8_12)),
% 0.20/0.51    inference(subsumption_resolution,[],[f199,f137])).
% 0.20/0.51  fof(f199,plain,(
% 0.20/0.51    sP5(sK4(sK2,sK1),sK2) | sK1 = k2_relat_1(sK2) | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | (~spl8_1 | ~spl8_10)),
% 0.20/0.51    inference(resolution,[],[f186,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f184,plain,(
% 0.20/0.51    ~spl8_3 | spl8_10),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f183])).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    $false | (~spl8_3 | spl8_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f182,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.51  fof(f182,plain,(
% 0.20/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl8_3 | spl8_10)),
% 0.20/0.51    inference(resolution,[],[f129,f85])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f83])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    spl8_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl8_10),
% 0.20/0.51    inference(resolution,[],[f127,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    ~v1_relat_1(sK2) | spl8_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f125])).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    spl8_15 | ~spl8_8 | ~spl8_13),
% 0.20/0.51    inference(avatar_split_clause,[],[f148,f140,f116,f150])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    spl8_8 <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    spl8_13 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.20/0.51  fof(f148,plain,(
% 0.20/0.51    sK0 = k1_relat_1(sK2) | (~spl8_8 | ~spl8_13)),
% 0.20/0.51    inference(backward_demodulation,[],[f118,f142])).
% 0.20/0.51  fof(f142,plain,(
% 0.20/0.51    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl8_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f140])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl8_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f116])).
% 0.20/0.51  fof(f147,plain,(
% 0.20/0.51    spl8_13 | spl8_14 | ~spl8_2 | ~spl8_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f98,f83,f78,f144,f140])).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    spl8_14 <=> k1_xboole_0 = sK1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    spl8_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl8_2 | ~spl8_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f93,f80])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    v1_funct_2(sK2,sK0,sK1) | ~spl8_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f78])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl8_3),
% 0.20/0.51    inference(resolution,[],[f85,f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(flattening,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    ~spl8_12 | spl8_4 | ~spl8_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f120,f111,f88,f135])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    spl8_4 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    spl8_7 <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    sK1 != k2_relat_1(sK2) | (spl8_4 | ~spl8_7)),
% 0.20/0.51    inference(superposition,[],[f90,f113])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl8_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f111])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    sK1 != k2_relset_1(sK0,sK1,sK2) | spl8_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f88])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    spl8_11 | ~spl8_10 | ~spl8_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f74,f69,f125,f131])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ( ! [X1] : (~v1_relat_1(sK2) | sP5(X1,sK2) | ~r2_hidden(X1,k2_relat_1(sK2))) ) | ~spl8_1),
% 0.20/0.51    inference(resolution,[],[f71,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | sP5(X2,X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.20/0.51    inference(equality_resolution,[],[f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP5(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    spl8_9 | ~spl8_10 | ~spl8_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f73,f69,f125,f122])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(sK2) | ~sP5(X0,sK2) | r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl8_1),
% 0.20/0.51    inference(resolution,[],[f71,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~sP5(X2,X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.20/0.51    inference(equality_resolution,[],[f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~sP5(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    spl8_8 | ~spl8_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f97,f83,f116])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl8_3),
% 0.20/0.51    inference(resolution,[],[f85,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    spl8_7 | ~spl8_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f96,f83,f111])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl8_3),
% 0.20/0.51    inference(resolution,[],[f85,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    spl8_6 | ~spl8_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f95,f83,f105])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    v5_relat_1(sK2,sK1) | ~spl8_3),
% 0.20/0.51    inference(resolution,[],[f85,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    ~spl8_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f33,f88])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    spl8_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f32,f83])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    spl8_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f31,f78])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    spl8_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f30,f69])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    v1_funct_1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (11227)------------------------------
% 0.20/0.51  % (11227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11227)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (11227)Memory used [KB]: 11001
% 0.20/0.51  % (11227)Time elapsed: 0.149 s
% 0.20/0.51  % (11227)------------------------------
% 0.20/0.51  % (11227)------------------------------
% 0.20/0.52  % (11230)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (11220)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (11223)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (11222)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (11207)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.39/0.52  % (11229)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.39/0.53  % (11214)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.39/0.53  % (11228)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.39/0.53  % (11208)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.39/0.53  % (11234)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.39/0.53  % (11233)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.39/0.53  % (11236)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.39/0.53  % (11231)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.39/0.54  % (11206)Success in time 0.193 s
%------------------------------------------------------------------------------
