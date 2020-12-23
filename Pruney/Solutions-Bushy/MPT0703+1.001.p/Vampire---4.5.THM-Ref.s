%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0703+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 188 expanded)
%              Number of leaves         :    9 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  176 ( 697 expanded)
%              Number of equality atoms :   16 (  35 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f208,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f102,f167,f180,f189,f207])).

fof(f207,plain,(
    ~ spl8_11 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | ~ spl8_11 ),
    inference(unit_resulting_resolution,[],[f17,f196,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f196,plain,
    ( r2_hidden(sK6(sK0,sK1),sK1)
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f193,f54])).

fof(f54,plain,(
    sK6(sK0,sK1) = k1_funct_1(sK2,sK4(sK2,sK6(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f14,f13,f51,f35])).

fof(f35,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f51,plain,(
    r2_hidden(sK6(sK0,sK1),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f16,f47,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,(
    r2_hidden(sK6(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f17,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f16,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f14,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f193,plain,
    ( r2_hidden(k1_funct_1(sK2,sK4(sK2,sK6(sK0,sK1))),sK1)
    | ~ spl8_11 ),
    inference(unit_resulting_resolution,[],[f14,f13,f158,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

fof(f158,plain,
    ( r2_hidden(sK4(sK2,sK6(sK0,sK1)),k10_relat_1(sK2,sK1))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl8_11
  <=> r2_hidden(sK4(sK2,sK6(sK0,sK1)),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f17,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f189,plain,(
    spl8_13 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | spl8_13 ),
    inference(unit_resulting_resolution,[],[f17,f166,f25])).

fof(f166,plain,
    ( ~ r2_hidden(sK6(sK0,sK1),sK0)
    | spl8_13 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl8_13
  <=> r2_hidden(sK6(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f180,plain,(
    spl8_12 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | spl8_12 ),
    inference(unit_resulting_resolution,[],[f14,f13,f51,f162,f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f162,plain,
    ( ~ r2_hidden(sK4(sK2,sK6(sK0,sK1)),k1_relat_1(sK2))
    | spl8_12 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl8_12
  <=> r2_hidden(sK4(sK2,sK6(sK0,sK1)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f167,plain,
    ( spl8_11
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f109,f100,f164,f160,f156])).

fof(f100,plain,
    ( spl8_5
  <=> ! [X7,X6] :
        ( ~ r2_hidden(X6,k1_relat_1(sK2))
        | r2_hidden(X6,k10_relat_1(sK2,X7))
        | ~ r2_hidden(k1_funct_1(sK2,X6),X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f109,plain,
    ( ~ r2_hidden(sK6(sK0,sK1),sK0)
    | ~ r2_hidden(sK4(sK2,sK6(sK0,sK1)),k1_relat_1(sK2))
    | r2_hidden(sK4(sK2,sK6(sK0,sK1)),k10_relat_1(sK2,sK1))
    | ~ spl8_5 ),
    inference(superposition,[],[f106,f54])).

fof(f106,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k1_funct_1(sK2,X2),sK0)
        | ~ r2_hidden(X2,k1_relat_1(sK2))
        | r2_hidden(X2,k10_relat_1(sK2,sK1)) )
    | ~ spl8_5 ),
    inference(resolution,[],[f101,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k10_relat_1(sK2,sK0))
      | r2_hidden(X0,k10_relat_1(sK2,sK1)) ) ),
    inference(resolution,[],[f15,f24])).

fof(f15,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f101,plain,
    ( ! [X6,X7] :
        ( r2_hidden(X6,k10_relat_1(sK2,X7))
        | ~ r2_hidden(X6,k1_relat_1(sK2))
        | ~ r2_hidden(k1_funct_1(sK2,X6),X7) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f102,plain,
    ( spl8_5
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f44,f73,f100])).

fof(f73,plain,
    ( spl8_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f44,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(X6,k1_relat_1(sK2))
      | ~ r2_hidden(k1_funct_1(sK2,X6),X7)
      | r2_hidden(X6,k10_relat_1(sK2,X7)) ) ),
    inference(resolution,[],[f14,f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(k1_funct_1(X0,X3),X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(k1_funct_1(X0,X3),X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f80,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f13,f75])).

fof(f75,plain,
    ( ~ v1_relat_1(sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f73])).

%------------------------------------------------------------------------------
