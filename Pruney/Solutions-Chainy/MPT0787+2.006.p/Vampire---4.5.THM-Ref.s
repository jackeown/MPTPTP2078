%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:04 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 246 expanded)
%              Number of leaves         :   31 ( 112 expanded)
%              Depth                    :    8
%              Number of atoms          :  423 ( 835 expanded)
%              Number of equality atoms :   38 (  71 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f577,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f72,f77,f82,f91,f92,f98,f104,f110,f116,f149,f194,f198,f219,f233,f447,f454,f499,f500,f504,f515,f570,f574,f575,f576])).

fof(f576,plain,
    ( sK0 != sK1
    | r2_hidden(sK1,k1_wellord1(sK2,sK1))
    | ~ r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f575,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ r2_hidden(sK1,k1_wellord1(sK2,sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f574,plain,
    ( ~ spl13_4
    | ~ spl13_45 ),
    inference(avatar_split_clause,[],[f571,f450,f79])).

fof(f79,plain,
    ( spl13_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f450,plain,
    ( spl13_45
  <=> r2_hidden(sK1,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_45])])).

fof(f571,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl13_45 ),
    inference(resolution,[],[f451,f62])).

fof(f62,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_wellord1(X0,X3))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | X1 != X3
      | ~ r2_hidden(X3,X2)
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(f451,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK1))
    | ~ spl13_45 ),
    inference(avatar_component_clause,[],[f450])).

fof(f570,plain,
    ( spl13_45
    | ~ spl13_6
    | ~ spl13_27 ),
    inference(avatar_split_clause,[],[f568,f261,f88,f450])).

fof(f88,plain,
    ( spl13_6
  <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f261,plain,
    ( spl13_27
  <=> r2_hidden(sK1,k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_27])])).

fof(f568,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK1))
    | ~ spl13_6
    | ~ spl13_27 ),
    inference(resolution,[],[f517,f89])).

fof(f89,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f517,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_wellord1(sK2,sK0),X0)
        | r2_hidden(sK1,X0) )
    | ~ spl13_27 ),
    inference(resolution,[],[f263,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f263,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl13_27 ),
    inference(avatar_component_clause,[],[f261])).

fof(f515,plain,
    ( spl13_27
    | ~ spl13_4
    | spl13_21
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f512,f229,f225,f79,f261])).

fof(f225,plain,
    ( spl13_21
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_21])])).

fof(f229,plain,
    ( spl13_22
  <=> r2_hidden(k4_tarski(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_22])])).

fof(f512,plain,
    ( sK0 = sK1
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl13_22 ),
    inference(resolution,[],[f231,f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X1),X0)
      | X1 = X3
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | X1 = X3
      | ~ r2_hidden(k4_tarski(X3,X1),X0)
      | r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f231,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ spl13_22 ),
    inference(avatar_component_clause,[],[f229])).

fof(f504,plain,
    ( spl13_44
    | spl13_6
    | ~ spl13_23 ),
    inference(avatar_split_clause,[],[f434,f235,f88,f436])).

fof(f436,plain,
    ( spl13_44
  <=> sK1 = sK12(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_44])])).

fof(f235,plain,
    ( spl13_23
  <=> ! [X1] :
        ( r1_tarski(k1_wellord1(sK2,sK0),X1)
        | r2_hidden(sK12(k1_wellord1(sK2,sK0),X1),k1_wellord1(sK2,sK1))
        | sK1 = sK12(k1_wellord1(sK2,sK0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_23])])).

fof(f434,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | sK1 = sK12(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl13_23 ),
    inference(duplicate_literal_removal,[],[f431])).

fof(f431,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | sK1 = sK12(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl13_23 ),
    inference(resolution,[],[f236,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK12(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f236,plain,
    ( ! [X1] :
        ( r2_hidden(sK12(k1_wellord1(sK2,sK0),X1),k1_wellord1(sK2,sK1))
        | r1_tarski(k1_wellord1(sK2,sK0),X1)
        | sK1 = sK12(k1_wellord1(sK2,sK0),X1) )
    | ~ spl13_23 ),
    inference(avatar_component_clause,[],[f235])).

fof(f500,plain,
    ( spl13_21
    | spl13_5
    | spl13_22
    | ~ spl13_1
    | ~ spl13_20 ),
    inference(avatar_split_clause,[],[f284,f217,f64,f229,f84,f225])).

fof(f84,plain,
    ( spl13_5
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f64,plain,
    ( spl13_1
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f217,plain,
    ( spl13_20
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X1,sK0),sK2)
        | r2_hidden(k4_tarski(sK0,X1),sK2)
        | sK0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).

fof(f284,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | sK0 = sK1
    | ~ spl13_1
    | ~ spl13_20 ),
    inference(resolution,[],[f218,f66])).

fof(f66,plain,
    ( r2_hidden(sK1,k3_relat_1(sK2))
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f218,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X1,sK0),sK2)
        | r2_hidden(k4_tarski(sK0,X1),sK2)
        | sK0 = X1 )
    | ~ spl13_20 ),
    inference(avatar_component_clause,[],[f217])).

fof(f499,plain,
    ( ~ spl13_4
    | spl13_23
    | ~ spl13_5
    | ~ spl13_17 ),
    inference(avatar_split_clause,[],[f497,f192,f84,f235,f79])).

fof(f192,plain,
    ( spl13_17
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k1_wellord1(sK2,X0),X1)
        | r2_hidden(k4_tarski(sK12(k1_wellord1(sK2,X0),X1),X2),sK2)
        | ~ r2_hidden(k4_tarski(X0,X2),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).

fof(f497,plain,
    ( ! [X7] :
        ( r1_tarski(k1_wellord1(sK2,sK0),X7)
        | sK1 = sK12(k1_wellord1(sK2,sK0),X7)
        | ~ v1_relat_1(sK2)
        | r2_hidden(sK12(k1_wellord1(sK2,sK0),X7),k1_wellord1(sK2,sK1)) )
    | ~ spl13_5
    | ~ spl13_17 ),
    inference(resolution,[],[f336,f59])).

fof(f336,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(sK12(k1_wellord1(sK2,sK0),X1),sK1),sK2)
        | r1_tarski(k1_wellord1(sK2,sK0),X1) )
    | ~ spl13_5
    | ~ spl13_17 ),
    inference(resolution,[],[f193,f85])).

fof(f85,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl13_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f193,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X2),sK2)
        | r2_hidden(k4_tarski(sK12(k1_wellord1(sK2,X0),X1),X2),sK2)
        | r1_tarski(k1_wellord1(sK2,X0),X1) )
    | ~ spl13_17 ),
    inference(avatar_component_clause,[],[f192])).

fof(f454,plain,
    ( spl13_6
    | spl13_27
    | ~ spl13_44 ),
    inference(avatar_split_clause,[],[f446,f436,f261,f88])).

fof(f446,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl13_44 ),
    inference(superposition,[],[f57,f438])).

fof(f438,plain,
    ( sK1 = sK12(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl13_44 ),
    inference(avatar_component_clause,[],[f436])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK12(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f447,plain,
    ( spl13_6
    | spl13_21
    | ~ spl13_5
    | ~ spl13_18
    | ~ spl13_44 ),
    inference(avatar_split_clause,[],[f440,f436,f196,f84,f225,f88])).

fof(f196,plain,
    ( spl13_18
  <=> ! [X3,X4] :
        ( r1_tarski(k1_wellord1(sK2,X3),X4)
        | sK12(k1_wellord1(sK2,X3),X4) = X3
        | ~ r2_hidden(k4_tarski(X3,sK12(k1_wellord1(sK2,X3),X4)),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f440,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | sK0 = sK1
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl13_18
    | ~ spl13_44 ),
    inference(superposition,[],[f197,f438])).

fof(f197,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(k4_tarski(X3,sK12(k1_wellord1(sK2,X3),X4)),sK2)
        | sK12(k1_wellord1(sK2,X3),X4) = X3
        | r1_tarski(k1_wellord1(sK2,X3),X4) )
    | ~ spl13_18 ),
    inference(avatar_component_clause,[],[f196])).

fof(f233,plain,
    ( sK0 != sK1
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(k4_tarski(sK1,sK1),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f219,plain,
    ( ~ spl13_10
    | spl13_20
    | ~ spl13_4
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f210,f69,f79,f217,f113])).

fof(f113,plain,
    ( spl13_10
  <=> v6_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f69,plain,
    ( spl13_2
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f210,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | sK0 = X1
        | r2_hidden(k4_tarski(sK0,X1),sK2)
        | r2_hidden(k4_tarski(X1,sK0),sK2)
        | ~ v6_relat_2(sK2) )
    | ~ spl13_2 ),
    inference(resolution,[],[f34,f71])).

fof(f71,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | X1 = X2
      | r2_hidden(k4_tarski(X1,X2),X0)
      | r2_hidden(k4_tarski(X2,X1),X0)
      | ~ v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f198,plain,
    ( ~ spl13_9
    | ~ spl13_4
    | spl13_18
    | ~ spl13_4 ),
    inference(avatar_split_clause,[],[f188,f79,f196,f79,f107])).

fof(f107,plain,
    ( spl13_9
  <=> v4_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f188,plain,
    ( ! [X4,X3] :
        ( r1_tarski(k1_wellord1(sK2,X3),X4)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(k4_tarski(X3,sK12(k1_wellord1(sK2,X3),X4)),sK2)
        | sK12(k1_wellord1(sK2,X3),X4) = X3
        | ~ v4_relat_2(sK2) )
    | ~ spl13_4 ),
    inference(resolution,[],[f186,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X2,X1),X0)
      | X1 = X2
      | ~ v4_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( ( r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).

fof(f186,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK12(k1_wellord1(sK2,X0),X1),X0),sK2)
        | r1_tarski(k1_wellord1(sK2,X0),X1) )
    | ~ spl13_4 ),
    inference(resolution,[],[f139,f81])).

fof(f81,plain,
    ( v1_relat_1(sK2)
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK12(k1_wellord1(X0,X1),X2),X1),X0)
      | r1_tarski(k1_wellord1(X0,X1),X2) ) ),
    inference(resolution,[],[f60,f57])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_wellord1(X0,X1))
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f194,plain,
    ( ~ spl13_8
    | ~ spl13_4
    | spl13_17
    | ~ spl13_4 ),
    inference(avatar_split_clause,[],[f187,f79,f192,f79,f101])).

fof(f101,plain,
    ( spl13_8
  <=> v8_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f187,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k1_wellord1(sK2,X0),X1)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(k4_tarski(X0,X2),sK2)
        | r2_hidden(k4_tarski(sK12(k1_wellord1(sK2,X0),X1),X2),sK2)
        | ~ v8_relat_2(sK2) )
    | ~ spl13_4 ),
    inference(resolution,[],[f186,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(k4_tarski(X1,X3),X0)
      | ~ v8_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => r2_hidden(k4_tarski(X1,X3),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_wellord1)).

fof(f149,plain,
    ( ~ spl13_7
    | spl13_12
    | ~ spl13_4
    | ~ spl13_1 ),
    inference(avatar_split_clause,[],[f142,f64,f79,f146,f95])).

fof(f95,plain,
    ( spl13_7
  <=> v1_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f146,plain,
    ( spl13_12
  <=> r2_hidden(k4_tarski(sK1,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f142,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK1,sK1),sK2)
    | ~ v1_relat_2(sK2)
    | ~ spl13_1 ),
    inference(resolution,[],[f27,f66])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

fof(f116,plain,
    ( ~ spl13_4
    | spl13_10
    | ~ spl13_3 ),
    inference(avatar_split_clause,[],[f111,f74,f113,f79])).

fof(f74,plain,
    ( spl13_3
  <=> v2_wellord1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f111,plain,
    ( v6_relat_2(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl13_3 ),
    inference(resolution,[],[f47,f76])).

fof(f76,plain,
    ( v2_wellord1(sK2)
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(f110,plain,
    ( ~ spl13_4
    | spl13_9
    | ~ spl13_3 ),
    inference(avatar_split_clause,[],[f105,f74,f107,f79])).

fof(f105,plain,
    ( v4_relat_2(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl13_3 ),
    inference(resolution,[],[f46,f76])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f104,plain,
    ( ~ spl13_4
    | spl13_8
    | ~ spl13_3 ),
    inference(avatar_split_clause,[],[f99,f74,f101,f79])).

fof(f99,plain,
    ( v8_relat_2(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl13_3 ),
    inference(resolution,[],[f45,f76])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f98,plain,
    ( ~ spl13_4
    | spl13_7
    | ~ spl13_3 ),
    inference(avatar_split_clause,[],[f93,f74,f95,f79])).

fof(f93,plain,
    ( v1_relat_2(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl13_3 ),
    inference(resolution,[],[f44,f76])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f92,plain,
    ( spl13_5
    | spl13_6 ),
    inference(avatar_split_clause,[],[f21,f88,f84])).

fof(f21,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => ( r2_hidden(k4_tarski(X0,X1),X2)
          <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).

fof(f91,plain,
    ( ~ spl13_5
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f22,f88,f84])).

fof(f22,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f82,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f23,f79])).

fof(f23,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f77,plain,(
    spl13_3 ),
    inference(avatar_split_clause,[],[f24,f74])).

fof(f24,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f72,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f25,f69])).

fof(f25,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f67,plain,(
    spl13_1 ),
    inference(avatar_split_clause,[],[f26,f64])).

fof(f26,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (17826)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (17799)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (17802)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (17808)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (17809)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (17818)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (17817)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (17823)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.53  % (17799)Refutation not found, incomplete strategy% (17799)------------------------------
% 1.31/0.53  % (17799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (17799)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (17799)Memory used [KB]: 10746
% 1.31/0.53  % (17799)Time elapsed: 0.116 s
% 1.31/0.53  % (17799)------------------------------
% 1.31/0.53  % (17799)------------------------------
% 1.31/0.53  % (17810)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.31/0.53  % (17801)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.53  % (17821)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.31/0.53  % (17803)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.31/0.53  % (17804)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.31/0.53  % (17807)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.31/0.53  % (17800)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.31/0.53  % (17820)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.53  % (17814)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.31/0.53  % (17798)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.53  % (17822)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.31/0.53  % (17814)Refutation not found, incomplete strategy% (17814)------------------------------
% 1.31/0.53  % (17814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (17814)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (17814)Memory used [KB]: 10618
% 1.31/0.53  % (17814)Time elapsed: 0.137 s
% 1.31/0.53  % (17814)------------------------------
% 1.31/0.53  % (17814)------------------------------
% 1.31/0.54  % (17797)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.54  % (17812)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.54  % (17813)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.54  % (17816)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.31/0.54  % (17815)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.54  % (17819)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.45/0.55  % (17805)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.45/0.55  % (17806)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.45/0.55  % (17811)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.45/0.55  % (17825)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.45/0.55  % (17824)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.45/0.57  % (17813)Refutation found. Thanks to Tanya!
% 1.45/0.57  % SZS status Theorem for theBenchmark
% 1.45/0.57  % SZS output start Proof for theBenchmark
% 1.45/0.57  fof(f577,plain,(
% 1.45/0.57    $false),
% 1.45/0.57    inference(avatar_sat_refutation,[],[f67,f72,f77,f82,f91,f92,f98,f104,f110,f116,f149,f194,f198,f219,f233,f447,f454,f499,f500,f504,f515,f570,f574,f575,f576])).
% 1.45/0.57  fof(f576,plain,(
% 1.45/0.57    sK0 != sK1 | r2_hidden(sK1,k1_wellord1(sK2,sK1)) | ~r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 1.45/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.45/0.57  fof(f575,plain,(
% 1.45/0.57    sK0 != sK1 | r2_hidden(sK0,k1_wellord1(sK2,sK1)) | ~r2_hidden(sK1,k1_wellord1(sK2,sK0))),
% 1.45/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.45/0.57  fof(f574,plain,(
% 1.45/0.57    ~spl13_4 | ~spl13_45),
% 1.45/0.57    inference(avatar_split_clause,[],[f571,f450,f79])).
% 1.45/0.57  fof(f79,plain,(
% 1.45/0.57    spl13_4 <=> v1_relat_1(sK2)),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).
% 1.45/0.57  fof(f450,plain,(
% 1.45/0.57    spl13_45 <=> r2_hidden(sK1,k1_wellord1(sK2,sK1))),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_45])])).
% 1.45/0.57  fof(f571,plain,(
% 1.45/0.57    ~v1_relat_1(sK2) | ~spl13_45),
% 1.45/0.57    inference(resolution,[],[f451,f62])).
% 1.45/0.57  fof(f62,plain,(
% 1.45/0.57    ( ! [X0,X3] : (~r2_hidden(X3,k1_wellord1(X0,X3)) | ~v1_relat_1(X0)) )),
% 1.45/0.57    inference(equality_resolution,[],[f61])).
% 1.45/0.57  fof(f61,plain,(
% 1.45/0.57    ( ! [X2,X0,X3] : (~v1_relat_1(X0) | ~r2_hidden(X3,X2) | k1_wellord1(X0,X3) != X2) )),
% 1.45/0.57    inference(equality_resolution,[],[f53])).
% 1.45/0.57  fof(f53,plain,(
% 1.45/0.57    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | X1 != X3 | ~r2_hidden(X3,X2) | k1_wellord1(X0,X1) != X2) )),
% 1.45/0.57    inference(cnf_transformation,[],[f19])).
% 1.45/0.57  fof(f19,plain,(
% 1.45/0.57    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 1.45/0.57    inference(ennf_transformation,[],[f2])).
% 1.45/0.57  fof(f2,axiom,(
% 1.45/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).
% 1.45/0.57  fof(f451,plain,(
% 1.45/0.57    r2_hidden(sK1,k1_wellord1(sK2,sK1)) | ~spl13_45),
% 1.45/0.57    inference(avatar_component_clause,[],[f450])).
% 1.45/0.57  fof(f570,plain,(
% 1.45/0.57    spl13_45 | ~spl13_6 | ~spl13_27),
% 1.45/0.57    inference(avatar_split_clause,[],[f568,f261,f88,f450])).
% 1.45/0.57  fof(f88,plain,(
% 1.45/0.57    spl13_6 <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).
% 1.45/0.57  fof(f261,plain,(
% 1.45/0.57    spl13_27 <=> r2_hidden(sK1,k1_wellord1(sK2,sK0))),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_27])])).
% 1.45/0.57  fof(f568,plain,(
% 1.45/0.57    r2_hidden(sK1,k1_wellord1(sK2,sK1)) | (~spl13_6 | ~spl13_27)),
% 1.45/0.57    inference(resolution,[],[f517,f89])).
% 1.45/0.57  fof(f89,plain,(
% 1.45/0.57    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl13_6),
% 1.45/0.57    inference(avatar_component_clause,[],[f88])).
% 1.45/0.57  fof(f517,plain,(
% 1.45/0.57    ( ! [X0] : (~r1_tarski(k1_wellord1(sK2,sK0),X0) | r2_hidden(sK1,X0)) ) | ~spl13_27),
% 1.45/0.57    inference(resolution,[],[f263,f56])).
% 1.45/0.57  fof(f56,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f20])).
% 1.45/0.57  fof(f20,plain,(
% 1.45/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.45/0.57    inference(ennf_transformation,[],[f1])).
% 1.45/0.57  fof(f1,axiom,(
% 1.45/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.45/0.57  fof(f263,plain,(
% 1.45/0.57    r2_hidden(sK1,k1_wellord1(sK2,sK0)) | ~spl13_27),
% 1.45/0.57    inference(avatar_component_clause,[],[f261])).
% 1.45/0.57  fof(f515,plain,(
% 1.45/0.57    spl13_27 | ~spl13_4 | spl13_21 | ~spl13_22),
% 1.45/0.57    inference(avatar_split_clause,[],[f512,f229,f225,f79,f261])).
% 1.45/0.57  fof(f225,plain,(
% 1.45/0.57    spl13_21 <=> sK0 = sK1),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_21])])).
% 1.45/0.57  fof(f229,plain,(
% 1.45/0.57    spl13_22 <=> r2_hidden(k4_tarski(sK1,sK0),sK2)),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_22])])).
% 1.45/0.57  fof(f512,plain,(
% 1.45/0.57    sK0 = sK1 | ~v1_relat_1(sK2) | r2_hidden(sK1,k1_wellord1(sK2,sK0)) | ~spl13_22),
% 1.45/0.57    inference(resolution,[],[f231,f59])).
% 1.45/0.57  fof(f59,plain,(
% 1.45/0.57    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~v1_relat_1(X0) | r2_hidden(X3,k1_wellord1(X0,X1))) )),
% 1.45/0.57    inference(equality_resolution,[],[f55])).
% 1.45/0.57  fof(f55,plain,(
% 1.45/0.57    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | X1 = X3 | ~r2_hidden(k4_tarski(X3,X1),X0) | r2_hidden(X3,X2) | k1_wellord1(X0,X1) != X2) )),
% 1.45/0.57    inference(cnf_transformation,[],[f19])).
% 1.45/0.57  fof(f231,plain,(
% 1.45/0.57    r2_hidden(k4_tarski(sK1,sK0),sK2) | ~spl13_22),
% 1.45/0.57    inference(avatar_component_clause,[],[f229])).
% 1.45/0.57  fof(f504,plain,(
% 1.45/0.57    spl13_44 | spl13_6 | ~spl13_23),
% 1.45/0.57    inference(avatar_split_clause,[],[f434,f235,f88,f436])).
% 1.45/0.57  fof(f436,plain,(
% 1.45/0.57    spl13_44 <=> sK1 = sK12(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_44])])).
% 1.45/0.57  fof(f235,plain,(
% 1.45/0.57    spl13_23 <=> ! [X1] : (r1_tarski(k1_wellord1(sK2,sK0),X1) | r2_hidden(sK12(k1_wellord1(sK2,sK0),X1),k1_wellord1(sK2,sK1)) | sK1 = sK12(k1_wellord1(sK2,sK0),X1))),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_23])])).
% 1.45/0.57  fof(f434,plain,(
% 1.45/0.57    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | sK1 = sK12(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl13_23),
% 1.45/0.57    inference(duplicate_literal_removal,[],[f431])).
% 1.45/0.57  fof(f431,plain,(
% 1.45/0.57    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | sK1 = sK12(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl13_23),
% 1.45/0.57    inference(resolution,[],[f236,f58])).
% 1.45/0.57  fof(f58,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~r2_hidden(sK12(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f20])).
% 1.45/0.57  fof(f236,plain,(
% 1.45/0.57    ( ! [X1] : (r2_hidden(sK12(k1_wellord1(sK2,sK0),X1),k1_wellord1(sK2,sK1)) | r1_tarski(k1_wellord1(sK2,sK0),X1) | sK1 = sK12(k1_wellord1(sK2,sK0),X1)) ) | ~spl13_23),
% 1.45/0.57    inference(avatar_component_clause,[],[f235])).
% 1.45/0.57  fof(f500,plain,(
% 1.45/0.57    spl13_21 | spl13_5 | spl13_22 | ~spl13_1 | ~spl13_20),
% 1.45/0.57    inference(avatar_split_clause,[],[f284,f217,f64,f229,f84,f225])).
% 1.45/0.57  fof(f84,plain,(
% 1.45/0.57    spl13_5 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).
% 1.45/0.57  fof(f64,plain,(
% 1.45/0.57    spl13_1 <=> r2_hidden(sK1,k3_relat_1(sK2))),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 1.45/0.57  fof(f217,plain,(
% 1.45/0.57    spl13_20 <=> ! [X1] : (~r2_hidden(X1,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X1,sK0),sK2) | r2_hidden(k4_tarski(sK0,X1),sK2) | sK0 = X1)),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).
% 1.45/0.57  fof(f284,plain,(
% 1.45/0.57    r2_hidden(k4_tarski(sK1,sK0),sK2) | r2_hidden(k4_tarski(sK0,sK1),sK2) | sK0 = sK1 | (~spl13_1 | ~spl13_20)),
% 1.45/0.57    inference(resolution,[],[f218,f66])).
% 1.45/0.57  fof(f66,plain,(
% 1.45/0.57    r2_hidden(sK1,k3_relat_1(sK2)) | ~spl13_1),
% 1.45/0.57    inference(avatar_component_clause,[],[f64])).
% 1.45/0.57  fof(f218,plain,(
% 1.45/0.57    ( ! [X1] : (~r2_hidden(X1,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X1,sK0),sK2) | r2_hidden(k4_tarski(sK0,X1),sK2) | sK0 = X1) ) | ~spl13_20),
% 1.45/0.57    inference(avatar_component_clause,[],[f217])).
% 1.45/0.57  fof(f499,plain,(
% 1.45/0.57    ~spl13_4 | spl13_23 | ~spl13_5 | ~spl13_17),
% 1.45/0.57    inference(avatar_split_clause,[],[f497,f192,f84,f235,f79])).
% 1.45/0.57  fof(f192,plain,(
% 1.45/0.57    spl13_17 <=> ! [X1,X0,X2] : (r1_tarski(k1_wellord1(sK2,X0),X1) | r2_hidden(k4_tarski(sK12(k1_wellord1(sK2,X0),X1),X2),sK2) | ~r2_hidden(k4_tarski(X0,X2),sK2))),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).
% 1.45/0.57  fof(f497,plain,(
% 1.45/0.57    ( ! [X7] : (r1_tarski(k1_wellord1(sK2,sK0),X7) | sK1 = sK12(k1_wellord1(sK2,sK0),X7) | ~v1_relat_1(sK2) | r2_hidden(sK12(k1_wellord1(sK2,sK0),X7),k1_wellord1(sK2,sK1))) ) | (~spl13_5 | ~spl13_17)),
% 1.45/0.57    inference(resolution,[],[f336,f59])).
% 1.45/0.57  fof(f336,plain,(
% 1.45/0.57    ( ! [X1] : (r2_hidden(k4_tarski(sK12(k1_wellord1(sK2,sK0),X1),sK1),sK2) | r1_tarski(k1_wellord1(sK2,sK0),X1)) ) | (~spl13_5 | ~spl13_17)),
% 1.45/0.57    inference(resolution,[],[f193,f85])).
% 1.45/0.57  fof(f85,plain,(
% 1.45/0.57    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl13_5),
% 1.45/0.57    inference(avatar_component_clause,[],[f84])).
% 1.45/0.57  fof(f193,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X2),sK2) | r2_hidden(k4_tarski(sK12(k1_wellord1(sK2,X0),X1),X2),sK2) | r1_tarski(k1_wellord1(sK2,X0),X1)) ) | ~spl13_17),
% 1.45/0.57    inference(avatar_component_clause,[],[f192])).
% 1.45/0.57  fof(f454,plain,(
% 1.45/0.57    spl13_6 | spl13_27 | ~spl13_44),
% 1.45/0.57    inference(avatar_split_clause,[],[f446,f436,f261,f88])).
% 1.45/0.57  fof(f446,plain,(
% 1.45/0.57    r2_hidden(sK1,k1_wellord1(sK2,sK0)) | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl13_44),
% 1.45/0.57    inference(superposition,[],[f57,f438])).
% 1.45/0.57  fof(f438,plain,(
% 1.45/0.57    sK1 = sK12(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl13_44),
% 1.45/0.57    inference(avatar_component_clause,[],[f436])).
% 1.45/0.57  fof(f57,plain,(
% 1.45/0.57    ( ! [X0,X1] : (r2_hidden(sK12(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f20])).
% 1.45/0.57  fof(f447,plain,(
% 1.45/0.57    spl13_6 | spl13_21 | ~spl13_5 | ~spl13_18 | ~spl13_44),
% 1.45/0.57    inference(avatar_split_clause,[],[f440,f436,f196,f84,f225,f88])).
% 1.45/0.57  fof(f196,plain,(
% 1.45/0.57    spl13_18 <=> ! [X3,X4] : (r1_tarski(k1_wellord1(sK2,X3),X4) | sK12(k1_wellord1(sK2,X3),X4) = X3 | ~r2_hidden(k4_tarski(X3,sK12(k1_wellord1(sK2,X3),X4)),sK2))),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).
% 1.45/0.57  fof(f440,plain,(
% 1.45/0.57    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | sK0 = sK1 | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | (~spl13_18 | ~spl13_44)),
% 1.45/0.57    inference(superposition,[],[f197,f438])).
% 1.45/0.57  fof(f197,plain,(
% 1.45/0.57    ( ! [X4,X3] : (~r2_hidden(k4_tarski(X3,sK12(k1_wellord1(sK2,X3),X4)),sK2) | sK12(k1_wellord1(sK2,X3),X4) = X3 | r1_tarski(k1_wellord1(sK2,X3),X4)) ) | ~spl13_18),
% 1.45/0.57    inference(avatar_component_clause,[],[f196])).
% 1.45/0.57  fof(f233,plain,(
% 1.45/0.57    sK0 != sK1 | r2_hidden(k4_tarski(sK0,sK1),sK2) | ~r2_hidden(k4_tarski(sK1,sK1),sK2)),
% 1.45/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.45/0.57  fof(f219,plain,(
% 1.45/0.57    ~spl13_10 | spl13_20 | ~spl13_4 | ~spl13_2),
% 1.45/0.57    inference(avatar_split_clause,[],[f210,f69,f79,f217,f113])).
% 1.45/0.57  fof(f113,plain,(
% 1.45/0.57    spl13_10 <=> v6_relat_2(sK2)),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).
% 1.45/0.57  fof(f69,plain,(
% 1.45/0.57    spl13_2 <=> r2_hidden(sK0,k3_relat_1(sK2))),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 1.45/0.57  fof(f210,plain,(
% 1.45/0.57    ( ! [X1] : (~v1_relat_1(sK2) | ~r2_hidden(X1,k3_relat_1(sK2)) | sK0 = X1 | r2_hidden(k4_tarski(sK0,X1),sK2) | r2_hidden(k4_tarski(X1,sK0),sK2) | ~v6_relat_2(sK2)) ) | ~spl13_2),
% 1.45/0.57    inference(resolution,[],[f34,f71])).
% 1.45/0.57  fof(f71,plain,(
% 1.45/0.57    r2_hidden(sK0,k3_relat_1(sK2)) | ~spl13_2),
% 1.45/0.57    inference(avatar_component_clause,[],[f69])).
% 1.45/0.57  fof(f34,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X1,k3_relat_1(X0)) | ~v1_relat_1(X0) | ~r2_hidden(X2,k3_relat_1(X0)) | X1 = X2 | r2_hidden(k4_tarski(X1,X2),X0) | r2_hidden(k4_tarski(X2,X1),X0) | ~v6_relat_2(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f15])).
% 1.45/0.57  fof(f15,plain,(
% 1.45/0.57    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 1.45/0.57    inference(ennf_transformation,[],[f7])).
% 1.45/0.57  fof(f7,axiom,(
% 1.45/0.57    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).
% 1.45/0.57  fof(f198,plain,(
% 1.45/0.57    ~spl13_9 | ~spl13_4 | spl13_18 | ~spl13_4),
% 1.45/0.57    inference(avatar_split_clause,[],[f188,f79,f196,f79,f107])).
% 1.45/0.57  fof(f107,plain,(
% 1.45/0.57    spl13_9 <=> v4_relat_2(sK2)),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).
% 1.45/0.57  fof(f188,plain,(
% 1.45/0.57    ( ! [X4,X3] : (r1_tarski(k1_wellord1(sK2,X3),X4) | ~v1_relat_1(sK2) | ~r2_hidden(k4_tarski(X3,sK12(k1_wellord1(sK2,X3),X4)),sK2) | sK12(k1_wellord1(sK2,X3),X4) = X3 | ~v4_relat_2(sK2)) ) | ~spl13_4),
% 1.45/0.57    inference(resolution,[],[f186,f30])).
% 1.45/0.57  fof(f30,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X2,X1),X0) | X1 = X2 | ~v4_relat_2(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f14])).
% 1.45/0.57  fof(f14,plain,(
% 1.45/0.57    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 1.45/0.57    inference(flattening,[],[f13])).
% 1.45/0.57  fof(f13,plain,(
% 1.45/0.57    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | (~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 1.45/0.57    inference(ennf_transformation,[],[f6])).
% 1.45/0.57  fof(f6,axiom,(
% 1.45/0.57    ! [X0] : (v1_relat_1(X0) => (v4_relat_2(X0) <=> ! [X1,X2] : ((r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => X1 = X2)))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).
% 1.45/0.57  fof(f186,plain,(
% 1.45/0.57    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK12(k1_wellord1(sK2,X0),X1),X0),sK2) | r1_tarski(k1_wellord1(sK2,X0),X1)) ) | ~spl13_4),
% 1.45/0.57    inference(resolution,[],[f139,f81])).
% 1.45/0.57  fof(f81,plain,(
% 1.45/0.57    v1_relat_1(sK2) | ~spl13_4),
% 1.45/0.57    inference(avatar_component_clause,[],[f79])).
% 1.45/0.57  fof(f139,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK12(k1_wellord1(X0,X1),X2),X1),X0) | r1_tarski(k1_wellord1(X0,X1),X2)) )),
% 1.45/0.57    inference(resolution,[],[f60,f57])).
% 1.45/0.57  fof(f60,plain,(
% 1.45/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_wellord1(X0,X1)) | r2_hidden(k4_tarski(X3,X1),X0) | ~v1_relat_1(X0)) )),
% 1.45/0.57    inference(equality_resolution,[],[f54])).
% 1.45/0.57  fof(f54,plain,(
% 1.45/0.57    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,X2) | k1_wellord1(X0,X1) != X2) )),
% 1.45/0.57    inference(cnf_transformation,[],[f19])).
% 1.45/0.57  fof(f194,plain,(
% 1.45/0.57    ~spl13_8 | ~spl13_4 | spl13_17 | ~spl13_4),
% 1.45/0.57    inference(avatar_split_clause,[],[f187,f79,f192,f79,f101])).
% 1.45/0.57  fof(f101,plain,(
% 1.45/0.57    spl13_8 <=> v8_relat_2(sK2)),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).
% 1.45/0.57  fof(f187,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (r1_tarski(k1_wellord1(sK2,X0),X1) | ~v1_relat_1(sK2) | ~r2_hidden(k4_tarski(X0,X2),sK2) | r2_hidden(k4_tarski(sK12(k1_wellord1(sK2,X0),X1),X2),sK2) | ~v8_relat_2(sK2)) ) | ~spl13_4),
% 1.45/0.57    inference(resolution,[],[f186,f40])).
% 1.45/0.57  fof(f40,plain,(
% 1.45/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(k4_tarski(X1,X3),X0) | ~v8_relat_2(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f17])).
% 1.45/0.57  fof(f17,plain,(
% 1.45/0.57    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 1.45/0.57    inference(flattening,[],[f16])).
% 1.45/0.57  fof(f16,plain,(
% 1.45/0.57    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | (~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 1.45/0.57    inference(ennf_transformation,[],[f5])).
% 1.45/0.57  fof(f5,axiom,(
% 1.45/0.57    ! [X0] : (v1_relat_1(X0) => (v8_relat_2(X0) <=> ! [X1,X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => r2_hidden(k4_tarski(X1,X3),X0))))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_wellord1)).
% 1.45/0.57  fof(f149,plain,(
% 1.45/0.57    ~spl13_7 | spl13_12 | ~spl13_4 | ~spl13_1),
% 1.45/0.57    inference(avatar_split_clause,[],[f142,f64,f79,f146,f95])).
% 1.45/0.57  fof(f95,plain,(
% 1.45/0.57    spl13_7 <=> v1_relat_2(sK2)),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).
% 1.45/0.57  fof(f146,plain,(
% 1.45/0.57    spl13_12 <=> r2_hidden(k4_tarski(sK1,sK1),sK2)),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).
% 1.45/0.57  fof(f142,plain,(
% 1.45/0.57    ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK1,sK1),sK2) | ~v1_relat_2(sK2) | ~spl13_1),
% 1.45/0.57    inference(resolution,[],[f27,f66])).
% 1.45/0.57  fof(f27,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k3_relat_1(X0)) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(X1,X1),X0) | ~v1_relat_2(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f12])).
% 1.45/0.57  fof(f12,plain,(
% 1.45/0.57    ! [X0] : ((v1_relat_2(X0) <=> ! [X1] : (r2_hidden(k4_tarski(X1,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 1.45/0.57    inference(ennf_transformation,[],[f4])).
% 1.45/0.57  fof(f4,axiom,(
% 1.45/0.57    ! [X0] : (v1_relat_1(X0) => (v1_relat_2(X0) <=> ! [X1] : (r2_hidden(X1,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X1),X0))))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).
% 1.45/0.57  fof(f116,plain,(
% 1.45/0.57    ~spl13_4 | spl13_10 | ~spl13_3),
% 1.45/0.57    inference(avatar_split_clause,[],[f111,f74,f113,f79])).
% 1.45/0.57  fof(f74,plain,(
% 1.45/0.57    spl13_3 <=> v2_wellord1(sK2)),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 1.45/0.57  fof(f111,plain,(
% 1.45/0.57    v6_relat_2(sK2) | ~v1_relat_1(sK2) | ~spl13_3),
% 1.45/0.57    inference(resolution,[],[f47,f76])).
% 1.45/0.57  fof(f76,plain,(
% 1.45/0.57    v2_wellord1(sK2) | ~spl13_3),
% 1.45/0.57    inference(avatar_component_clause,[],[f74])).
% 1.45/0.57  fof(f47,plain,(
% 1.45/0.57    ( ! [X0] : (~v2_wellord1(X0) | v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f18])).
% 1.45/0.57  fof(f18,plain,(
% 1.45/0.57    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.45/0.57    inference(ennf_transformation,[],[f3])).
% 1.45/0.57  fof(f3,axiom,(
% 1.45/0.57    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).
% 1.45/0.57  fof(f110,plain,(
% 1.45/0.57    ~spl13_4 | spl13_9 | ~spl13_3),
% 1.45/0.57    inference(avatar_split_clause,[],[f105,f74,f107,f79])).
% 1.45/0.57  fof(f105,plain,(
% 1.45/0.57    v4_relat_2(sK2) | ~v1_relat_1(sK2) | ~spl13_3),
% 1.45/0.57    inference(resolution,[],[f46,f76])).
% 1.45/0.57  fof(f46,plain,(
% 1.45/0.57    ( ! [X0] : (~v2_wellord1(X0) | v4_relat_2(X0) | ~v1_relat_1(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f18])).
% 1.45/0.57  fof(f104,plain,(
% 1.45/0.57    ~spl13_4 | spl13_8 | ~spl13_3),
% 1.45/0.57    inference(avatar_split_clause,[],[f99,f74,f101,f79])).
% 1.45/0.57  fof(f99,plain,(
% 1.45/0.57    v8_relat_2(sK2) | ~v1_relat_1(sK2) | ~spl13_3),
% 1.45/0.57    inference(resolution,[],[f45,f76])).
% 1.45/0.57  fof(f45,plain,(
% 1.45/0.57    ( ! [X0] : (~v2_wellord1(X0) | v8_relat_2(X0) | ~v1_relat_1(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f18])).
% 1.45/0.57  fof(f98,plain,(
% 1.45/0.57    ~spl13_4 | spl13_7 | ~spl13_3),
% 1.45/0.57    inference(avatar_split_clause,[],[f93,f74,f95,f79])).
% 1.45/0.57  fof(f93,plain,(
% 1.45/0.57    v1_relat_2(sK2) | ~v1_relat_1(sK2) | ~spl13_3),
% 1.45/0.57    inference(resolution,[],[f44,f76])).
% 1.45/0.57  fof(f44,plain,(
% 1.45/0.57    ( ! [X0] : (~v2_wellord1(X0) | v1_relat_2(X0) | ~v1_relat_1(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f18])).
% 1.45/0.57  fof(f92,plain,(
% 1.45/0.57    spl13_5 | spl13_6),
% 1.45/0.57    inference(avatar_split_clause,[],[f21,f88,f84])).
% 1.45/0.57  fof(f21,plain,(
% 1.45/0.57    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 1.45/0.57    inference(cnf_transformation,[],[f11])).
% 1.45/0.57  fof(f11,plain,(
% 1.45/0.57    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 1.45/0.57    inference(flattening,[],[f10])).
% 1.45/0.57  fof(f10,plain,(
% 1.45/0.57    ? [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 1.45/0.57    inference(ennf_transformation,[],[f9])).
% 1.45/0.57  fof(f9,negated_conjecture,(
% 1.45/0.57    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 1.45/0.57    inference(negated_conjecture,[],[f8])).
% 1.45/0.57  fof(f8,conjecture,(
% 1.45/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).
% 1.45/0.57  fof(f91,plain,(
% 1.45/0.57    ~spl13_5 | ~spl13_6),
% 1.45/0.57    inference(avatar_split_clause,[],[f22,f88,f84])).
% 1.45/0.57  fof(f22,plain,(
% 1.45/0.57    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 1.45/0.57    inference(cnf_transformation,[],[f11])).
% 1.45/0.57  fof(f82,plain,(
% 1.45/0.57    spl13_4),
% 1.45/0.57    inference(avatar_split_clause,[],[f23,f79])).
% 1.45/0.57  fof(f23,plain,(
% 1.45/0.57    v1_relat_1(sK2)),
% 1.45/0.57    inference(cnf_transformation,[],[f11])).
% 1.45/0.57  fof(f77,plain,(
% 1.45/0.57    spl13_3),
% 1.45/0.57    inference(avatar_split_clause,[],[f24,f74])).
% 1.45/0.57  fof(f24,plain,(
% 1.45/0.57    v2_wellord1(sK2)),
% 1.45/0.57    inference(cnf_transformation,[],[f11])).
% 1.45/0.57  fof(f72,plain,(
% 1.45/0.57    spl13_2),
% 1.45/0.57    inference(avatar_split_clause,[],[f25,f69])).
% 1.45/0.57  fof(f25,plain,(
% 1.45/0.57    r2_hidden(sK0,k3_relat_1(sK2))),
% 1.45/0.57    inference(cnf_transformation,[],[f11])).
% 1.45/0.57  fof(f67,plain,(
% 1.45/0.57    spl13_1),
% 1.45/0.57    inference(avatar_split_clause,[],[f26,f64])).
% 1.45/0.57  fof(f26,plain,(
% 1.45/0.57    r2_hidden(sK1,k3_relat_1(sK2))),
% 1.45/0.57    inference(cnf_transformation,[],[f11])).
% 1.45/0.57  % SZS output end Proof for theBenchmark
% 1.45/0.57  % (17813)------------------------------
% 1.45/0.57  % (17813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (17813)Termination reason: Refutation
% 1.45/0.57  
% 1.45/0.57  % (17813)Memory used [KB]: 11129
% 1.45/0.57  % (17813)Time elapsed: 0.173 s
% 1.45/0.57  % (17813)------------------------------
% 1.45/0.57  % (17813)------------------------------
% 1.45/0.57  % (17796)Success in time 0.212 s
%------------------------------------------------------------------------------
