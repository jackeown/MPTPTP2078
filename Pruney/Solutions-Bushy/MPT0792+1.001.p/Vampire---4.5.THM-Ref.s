%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0792+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:39 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 132 expanded)
%              Number of leaves         :   17 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :  255 ( 505 expanded)
%              Number of equality atoms :   22 (  47 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f171,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f53,f72,f76,f84,f112,f116,f125,f138,f139,f158,f170])).

fof(f170,plain,
    ( ~ spl8_1
    | spl8_11
    | ~ spl8_16 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl8_1
    | spl8_11
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f168,f115])).

fof(f115,plain,
    ( ~ r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | spl8_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl8_11
  <=> r2_hidden(sK1,k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f168,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl8_1
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f167,f48])).

fof(f48,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl8_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f167,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl8_16 ),
    inference(resolution,[],[f157,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
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

fof(f157,plain,
    ( sP4(sK1,sK0,sK2)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl8_16
  <=> sP4(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f158,plain,
    ( spl8_16
    | spl8_15
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f143,f133,f136,f156])).

fof(f136,plain,
    ( spl8_15
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f133,plain,
    ( spl8_14
  <=> r2_hidden(k4_tarski(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f143,plain,
    ( sK0 = sK1
    | sP4(sK1,sK0,sK2)
    | ~ spl8_14 ),
    inference(resolution,[],[f134,f20])).

fof(f20,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X1),X0)
      | X1 = X3
      | sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f134,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f133])).

fof(f139,plain,
    ( sK0 != sK1
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(k4_tarski(sK1,sK1),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f138,plain,
    ( spl8_14
    | spl8_15
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | spl8_10 ),
    inference(avatar_split_clause,[],[f131,f110,f82,f74,f51,f47,f136,f133])).

fof(f51,plain,
    ( spl8_2
  <=> v2_wellord1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f74,plain,
    ( spl8_4
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f82,plain,
    ( spl8_6
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f110,plain,
    ( spl8_10
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f131,plain,
    ( sK0 = sK1
    | r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | spl8_10 ),
    inference(subsumption_resolution,[],[f129,f111])).

fof(f111,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f129,plain,
    ( sK0 = sK1
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(resolution,[],[f94,f83])).

fof(f83,plain,
    ( r2_hidden(sK1,k3_relat_1(sK2))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | sK0 = X0
        | r2_hidden(k4_tarski(sK0,X0),sK2)
        | r2_hidden(k4_tarski(X0,sK0),sK2) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f93,f67])).

fof(f67,plain,
    ( v6_relat_2(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f62,f48])).

fof(f62,plain,
    ( v6_relat_2(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_2 ),
    inference(resolution,[],[f52,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f52,plain,
    ( v2_wellord1(sK2)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | sK0 = X0
        | r2_hidden(k4_tarski(sK0,X0),sK2)
        | r2_hidden(k4_tarski(X0,sK0),sK2)
        | ~ v6_relat_2(sK2) )
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f90,f48])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | sK0 = X0
        | r2_hidden(k4_tarski(sK0,X0),sK2)
        | r2_hidden(k4_tarski(X0,sK0),sK2)
        | ~ v6_relat_2(sK2) )
    | ~ spl8_4 ),
    inference(resolution,[],[f75,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | X1 = X2
      | r2_hidden(k4_tarski(X1,X2),X0)
      | r2_hidden(k4_tarski(X2,X1),X0)
      | ~ v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

fof(f75,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f125,plain,
    ( spl8_13
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f102,f82,f70,f47,f123])).

fof(f123,plain,
    ( spl8_13
  <=> r2_hidden(k4_tarski(sK1,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f70,plain,
    ( spl8_3
  <=> v1_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f102,plain,
    ( r2_hidden(k4_tarski(sK1,sK1),sK2)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f101,f71])).

fof(f71,plain,
    ( v1_relat_2(sK2)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f101,plain,
    ( r2_hidden(k4_tarski(sK1,sK1),sK2)
    | ~ v1_relat_2(sK2)
    | ~ spl8_1
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f99,f48])).

fof(f99,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK1,sK1),sK2)
    | ~ v1_relat_2(sK2)
    | ~ spl8_6 ),
    inference(resolution,[],[f83,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X1,X1),X0)
      | ~ v1_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f116,plain,(
    ~ spl8_11 ),
    inference(avatar_split_clause,[],[f42,f114])).

fof(f42,plain,(
    ~ r2_hidden(sK1,k1_wellord1(sK2,sK0)) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_wellord1(sK2,sK0))
      | sK1 != X3 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      & ! [X3] :
          ( ( X1 != X3
            & r2_hidden(k4_tarski(X3,X1),X2) )
          | ~ r2_hidden(X3,k1_wellord1(X2,X0)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      & ! [X3] :
          ( ( X1 != X3
            & r2_hidden(k4_tarski(X3,X1),X2) )
          | ~ r2_hidden(X3,k1_wellord1(X2,X0)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( ! [X3] :
                ( r2_hidden(X3,k1_wellord1(X2,X0))
               => ( X1 != X3
                  & r2_hidden(k4_tarski(X3,X1),X2) ) )
            & r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => r2_hidden(k4_tarski(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( ! [X3] :
              ( r2_hidden(X3,k1_wellord1(X2,X0))
             => ( X1 != X3
                & r2_hidden(k4_tarski(X3,X1),X2) ) )
          & r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => r2_hidden(k4_tarski(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_wellord1)).

fof(f112,plain,(
    ~ spl8_10 ),
    inference(avatar_split_clause,[],[f19,f110])).

fof(f19,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f84,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f18,f82])).

fof(f18,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f76,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f17,f74])).

fof(f17,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f72,plain,
    ( spl8_3
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f64,f51,f47,f70])).

fof(f64,plain,
    ( v1_relat_2(sK2)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f59,f48])).

fof(f59,plain,
    ( v1_relat_2(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_2 ),
    inference(resolution,[],[f52,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f16,f51])).

fof(f16,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f49,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f15,f47])).

fof(f15,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
