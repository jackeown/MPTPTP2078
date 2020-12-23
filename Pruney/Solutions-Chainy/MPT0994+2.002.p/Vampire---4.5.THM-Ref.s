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
% DateTime   : Thu Dec  3 13:03:28 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 160 expanded)
%              Number of leaves         :   22 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  350 ( 650 expanded)
%              Number of equality atoms :   88 ( 180 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f59,f67,f71,f77,f90,f99,f110,f115,f127,f160,f172,f187,f188])).

fof(f188,plain,
    ( k1_xboole_0 != k1_funct_1(sK4,sK2)
    | k1_xboole_0 != k1_funct_1(k8_relat_1(sK3,sK4),sK2)
    | k1_funct_1(sK4,sK2) = k1_funct_1(k8_relat_1(sK3,sK4),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f187,plain,
    ( spl5_7
    | ~ spl5_3
    | ~ spl5_14
    | spl5_22 ),
    inference(avatar_split_clause,[],[f180,f170,f125,f57,f75])).

fof(f75,plain,
    ( spl5_7
  <=> k1_funct_1(sK4,sK2) = k1_funct_1(k8_relat_1(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f57,plain,
    ( spl5_3
  <=> r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f125,plain,
    ( spl5_14
  <=> ! [X3,X4] :
        ( k1_funct_1(sK4,X3) = k1_funct_1(k8_relat_1(X4,sK4),X3)
        | k1_xboole_0 = k1_funct_1(sK4,X3)
        | ~ r2_hidden(k1_funct_1(sK4,X3),X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f170,plain,
    ( spl5_22
  <=> k1_xboole_0 = k1_funct_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f180,plain,
    ( k1_funct_1(sK4,sK2) = k1_funct_1(k8_relat_1(sK3,sK4),sK2)
    | ~ spl5_3
    | ~ spl5_14
    | spl5_22 ),
    inference(resolution,[],[f175,f58])).

fof(f58,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2),sK3)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK4,sK2),X0)
        | k1_funct_1(sK4,sK2) = k1_funct_1(k8_relat_1(X0,sK4),sK2) )
    | ~ spl5_14
    | spl5_22 ),
    inference(trivial_inequality_removal,[],[f174])).

fof(f174,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_funct_1(sK4,sK2) = k1_funct_1(k8_relat_1(X0,sK4),sK2)
        | ~ r2_hidden(k1_funct_1(sK4,sK2),X0) )
    | ~ spl5_14
    | spl5_22 ),
    inference(superposition,[],[f171,f126])).

fof(f126,plain,
    ( ! [X4,X3] :
        ( k1_xboole_0 = k1_funct_1(sK4,X3)
        | k1_funct_1(sK4,X3) = k1_funct_1(k8_relat_1(X4,sK4),X3)
        | ~ r2_hidden(k1_funct_1(sK4,X3),X4) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f125])).

fof(f171,plain,
    ( k1_xboole_0 != k1_funct_1(sK4,sK2)
    | spl5_22 ),
    inference(avatar_component_clause,[],[f170])).

fof(f172,plain,
    ( spl5_21
    | ~ spl5_22
    | spl5_7
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f165,f158,f75,f170,f167])).

fof(f167,plain,
    ( spl5_21
  <=> k1_xboole_0 = k1_funct_1(k8_relat_1(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f158,plain,
    ( spl5_20
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k1_funct_1(k8_relat_1(X0,sK4),X1)
        | k1_funct_1(k8_relat_1(X0,sK4),X1) = k1_funct_1(sK4,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f165,plain,
    ( k1_xboole_0 != k1_funct_1(sK4,sK2)
    | k1_xboole_0 = k1_funct_1(k8_relat_1(sK3,sK4),sK2)
    | spl5_7
    | ~ spl5_20 ),
    inference(inner_rewriting,[],[f161])).

fof(f161,plain,
    ( k1_xboole_0 != k1_funct_1(sK4,sK2)
    | k1_funct_1(sK4,sK2) = k1_funct_1(k8_relat_1(sK3,sK4),sK2)
    | spl5_7
    | ~ spl5_20 ),
    inference(superposition,[],[f76,f159])).

fof(f159,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k1_funct_1(k8_relat_1(X0,sK4),X1)
        | k1_funct_1(k8_relat_1(X0,sK4),X1) = k1_funct_1(sK4,X1) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f158])).

fof(f76,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k8_relat_1(sK3,sK4),sK2)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f160,plain,
    ( ~ spl5_8
    | ~ spl5_6
    | spl5_20
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f155,f108,f158,f69,f81])).

fof(f81,plain,
    ( spl5_8
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f69,plain,
    ( spl5_6
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f108,plain,
    ( spl5_11
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k1_funct_1(k8_relat_1(X0,sK4),X1)
        | ~ v1_relat_1(k8_relat_1(X0,sK4))
        | k1_funct_1(k8_relat_1(X0,sK4),X1) = k1_funct_1(sK4,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f155,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k1_funct_1(k8_relat_1(X0,sK4),X1)
        | k1_funct_1(k8_relat_1(X0,sK4),X1) = k1_funct_1(sK4,X1)
        | ~ v1_funct_1(sK4)
        | ~ v1_relat_1(sK4) )
    | ~ spl5_11 ),
    inference(resolution,[],[f109,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_funct_1)).

fof(f109,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k8_relat_1(X0,sK4))
        | k1_xboole_0 = k1_funct_1(k8_relat_1(X0,sK4),X1)
        | k1_funct_1(k8_relat_1(X0,sK4),X1) = k1_funct_1(sK4,X1) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f127,plain,
    ( ~ spl5_8
    | ~ spl5_6
    | spl5_14
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f117,f113,f125,f69,f81])).

fof(f113,plain,
    ( spl5_12
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k1_funct_1(sK4,X0),X1)
        | k1_funct_1(sK4,X0) = k1_funct_1(k8_relat_1(X1,sK4),X0)
        | ~ r2_hidden(X0,k1_relat_1(sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f117,plain,
    ( ! [X4,X3] :
        ( k1_funct_1(sK4,X3) = k1_funct_1(k8_relat_1(X4,sK4),X3)
        | ~ r2_hidden(k1_funct_1(sK4,X3),X4)
        | k1_xboole_0 = k1_funct_1(sK4,X3)
        | ~ v1_funct_1(sK4)
        | ~ v1_relat_1(sK4) )
    | ~ spl5_12 ),
    inference(resolution,[],[f114,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_relat_1(X0))
      | k1_funct_1(X0,X1) = k1_xboole_0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK4))
        | k1_funct_1(sK4,X0) = k1_funct_1(k8_relat_1(X1,sK4),X0)
        | ~ r2_hidden(k1_funct_1(sK4,X0),X1) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f113])).

fof(f115,plain,
    ( ~ spl5_8
    | ~ spl5_6
    | spl5_12
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f111,f97,f113,f69,f81])).

fof(f97,plain,
    ( spl5_10
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4)))
        | k1_funct_1(sK4,X0) = k1_funct_1(k8_relat_1(X1,sK4),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_funct_1(sK4,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(sK4))
        | ~ v1_funct_1(sK4)
        | ~ v1_relat_1(sK4)
        | k1_funct_1(sK4,X0) = k1_funct_1(k8_relat_1(X1,sK4),X0) )
    | ~ spl5_10 ),
    inference(resolution,[],[f43,f98])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4)))
        | k1_funct_1(sK4,X0) = k1_funct_1(k8_relat_1(X1,sK4),X0) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ r2_hidden(k1_funct_1(X2,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_funct_1)).

fof(f110,plain,
    ( ~ spl5_8
    | ~ spl5_6
    | spl5_11
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f105,f97,f108,f69,f81])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k1_funct_1(k8_relat_1(X0,sK4),X1)
        | k1_funct_1(k8_relat_1(X0,sK4),X1) = k1_funct_1(sK4,X1)
        | ~ v1_relat_1(k8_relat_1(X0,sK4))
        | ~ v1_funct_1(sK4)
        | ~ v1_relat_1(sK4) )
    | ~ spl5_10 ),
    inference(resolution,[],[f102,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k8_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f102,plain,
    ( ! [X4,X3] :
        ( ~ v1_funct_1(k8_relat_1(X4,sK4))
        | k1_xboole_0 = k1_funct_1(k8_relat_1(X4,sK4),X3)
        | k1_funct_1(sK4,X3) = k1_funct_1(k8_relat_1(X4,sK4),X3)
        | ~ v1_relat_1(k8_relat_1(X4,sK4)) )
    | ~ spl5_10 ),
    inference(resolution,[],[f98,f45])).

fof(f99,plain,
    ( ~ spl5_8
    | spl5_10
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f94,f69,f97,f81])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4)))
        | k1_funct_1(sK4,X0) = k1_funct_1(k8_relat_1(X1,sK4),X0)
        | ~ v1_relat_1(sK4) )
    | ~ spl5_6 ),
    inference(resolution,[],[f40,f70])).

fof(f70,plain,
    ( v1_funct_1(sK4)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
       => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_1)).

fof(f90,plain,
    ( ~ spl5_5
    | spl5_8 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | ~ spl5_5
    | spl5_8 ),
    inference(subsumption_resolution,[],[f66,f88])).

fof(f88,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_8 ),
    inference(resolution,[],[f82,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f82,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f81])).

fof(f66,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl5_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f77,plain,
    ( ~ spl5_7
    | spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f73,f65,f49,f75])).

fof(f49,plain,
    ( spl5_1
  <=> k1_funct_1(sK4,sK2) = k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f73,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k8_relat_1(sK3,sK4),sK2)
    | spl5_1
    | ~ spl5_5 ),
    inference(superposition,[],[f50,f72])).

fof(f72,plain,
    ( ! [X0] : k6_relset_1(sK0,sK1,X0,sK4) = k8_relat_1(X0,sK4)
    | ~ spl5_5 ),
    inference(resolution,[],[f44,f66])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(f50,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f71,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f27,f69])).

fof(f27,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2)
    & k1_xboole_0 != sK1
    & r2_hidden(k1_funct_1(sK4,sK2),sK3)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f11,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
        & k1_xboole_0 != X1
        & r2_hidden(k1_funct_1(X4,X2),X3)
        & r2_hidden(X2,X0)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
   => ( k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2)
      & k1_xboole_0 != sK1
      & r2_hidden(k1_funct_1(sK4,sK2),sK3)
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
      & k1_xboole_0 != X1
      & r2_hidden(k1_funct_1(X4,X2),X3)
      & r2_hidden(X2,X0)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X4) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
      & k1_xboole_0 != X1
      & r2_hidden(k1_funct_1(X4,X2),X3)
      & r2_hidden(X2,X0)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X4) )
       => ( ( r2_hidden(k1_funct_1(X4,X2),X3)
            & r2_hidden(X2,X0) )
         => ( k1_funct_1(X4,X2) = k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X4,X0,X1)
          & v1_funct_1(X4) )
       => ( ( r2_hidden(k1_funct_1(X4,X2),X3)
            & r2_hidden(X2,X0) )
         => ( k1_funct_1(X4,X2) = k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4) )
     => ( ( r2_hidden(k1_funct_1(X4,X2),X3)
          & r2_hidden(X2,X0) )
       => ( k1_funct_1(X4,X2) = k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_funct_2)).

fof(f67,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f28,f65])).

fof(f28,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f30,f57])).

fof(f30,plain,(
    r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f32,f49])).

fof(f32,plain,(
    k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:12:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.43  % (9577)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.44  % (9569)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.45  % (9569)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  fof(f189,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(avatar_sat_refutation,[],[f51,f59,f67,f71,f77,f90,f99,f110,f115,f127,f160,f172,f187,f188])).
% 0.19/0.45  fof(f188,plain,(
% 0.19/0.45    k1_xboole_0 != k1_funct_1(sK4,sK2) | k1_xboole_0 != k1_funct_1(k8_relat_1(sK3,sK4),sK2) | k1_funct_1(sK4,sK2) = k1_funct_1(k8_relat_1(sK3,sK4),sK2)),
% 0.19/0.45    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.45  fof(f187,plain,(
% 0.19/0.45    spl5_7 | ~spl5_3 | ~spl5_14 | spl5_22),
% 0.19/0.45    inference(avatar_split_clause,[],[f180,f170,f125,f57,f75])).
% 0.19/0.45  fof(f75,plain,(
% 0.19/0.45    spl5_7 <=> k1_funct_1(sK4,sK2) = k1_funct_1(k8_relat_1(sK3,sK4),sK2)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.19/0.45  fof(f57,plain,(
% 0.19/0.45    spl5_3 <=> r2_hidden(k1_funct_1(sK4,sK2),sK3)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.45  fof(f125,plain,(
% 0.19/0.45    spl5_14 <=> ! [X3,X4] : (k1_funct_1(sK4,X3) = k1_funct_1(k8_relat_1(X4,sK4),X3) | k1_xboole_0 = k1_funct_1(sK4,X3) | ~r2_hidden(k1_funct_1(sK4,X3),X4))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.19/0.45  fof(f170,plain,(
% 0.19/0.45    spl5_22 <=> k1_xboole_0 = k1_funct_1(sK4,sK2)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.19/0.45  fof(f180,plain,(
% 0.19/0.45    k1_funct_1(sK4,sK2) = k1_funct_1(k8_relat_1(sK3,sK4),sK2) | (~spl5_3 | ~spl5_14 | spl5_22)),
% 0.19/0.45    inference(resolution,[],[f175,f58])).
% 0.19/0.45  fof(f58,plain,(
% 0.19/0.45    r2_hidden(k1_funct_1(sK4,sK2),sK3) | ~spl5_3),
% 0.19/0.45    inference(avatar_component_clause,[],[f57])).
% 0.19/0.45  fof(f175,plain,(
% 0.19/0.45    ( ! [X0] : (~r2_hidden(k1_funct_1(sK4,sK2),X0) | k1_funct_1(sK4,sK2) = k1_funct_1(k8_relat_1(X0,sK4),sK2)) ) | (~spl5_14 | spl5_22)),
% 0.19/0.45    inference(trivial_inequality_removal,[],[f174])).
% 0.19/0.45  fof(f174,plain,(
% 0.19/0.45    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_funct_1(sK4,sK2) = k1_funct_1(k8_relat_1(X0,sK4),sK2) | ~r2_hidden(k1_funct_1(sK4,sK2),X0)) ) | (~spl5_14 | spl5_22)),
% 0.19/0.45    inference(superposition,[],[f171,f126])).
% 0.19/0.45  fof(f126,plain,(
% 0.19/0.45    ( ! [X4,X3] : (k1_xboole_0 = k1_funct_1(sK4,X3) | k1_funct_1(sK4,X3) = k1_funct_1(k8_relat_1(X4,sK4),X3) | ~r2_hidden(k1_funct_1(sK4,X3),X4)) ) | ~spl5_14),
% 0.19/0.45    inference(avatar_component_clause,[],[f125])).
% 0.19/0.45  fof(f171,plain,(
% 0.19/0.45    k1_xboole_0 != k1_funct_1(sK4,sK2) | spl5_22),
% 0.19/0.45    inference(avatar_component_clause,[],[f170])).
% 0.19/0.45  fof(f172,plain,(
% 0.19/0.45    spl5_21 | ~spl5_22 | spl5_7 | ~spl5_20),
% 0.19/0.45    inference(avatar_split_clause,[],[f165,f158,f75,f170,f167])).
% 0.19/0.45  fof(f167,plain,(
% 0.19/0.45    spl5_21 <=> k1_xboole_0 = k1_funct_1(k8_relat_1(sK3,sK4),sK2)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.19/0.45  fof(f158,plain,(
% 0.19/0.45    spl5_20 <=> ! [X1,X0] : (k1_xboole_0 = k1_funct_1(k8_relat_1(X0,sK4),X1) | k1_funct_1(k8_relat_1(X0,sK4),X1) = k1_funct_1(sK4,X1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.19/0.45  fof(f165,plain,(
% 0.19/0.45    k1_xboole_0 != k1_funct_1(sK4,sK2) | k1_xboole_0 = k1_funct_1(k8_relat_1(sK3,sK4),sK2) | (spl5_7 | ~spl5_20)),
% 0.19/0.45    inference(inner_rewriting,[],[f161])).
% 0.19/0.45  fof(f161,plain,(
% 0.19/0.45    k1_xboole_0 != k1_funct_1(sK4,sK2) | k1_funct_1(sK4,sK2) = k1_funct_1(k8_relat_1(sK3,sK4),sK2) | (spl5_7 | ~spl5_20)),
% 0.19/0.45    inference(superposition,[],[f76,f159])).
% 0.19/0.45  fof(f159,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k1_xboole_0 = k1_funct_1(k8_relat_1(X0,sK4),X1) | k1_funct_1(k8_relat_1(X0,sK4),X1) = k1_funct_1(sK4,X1)) ) | ~spl5_20),
% 0.19/0.45    inference(avatar_component_clause,[],[f158])).
% 0.19/0.45  fof(f76,plain,(
% 0.19/0.45    k1_funct_1(sK4,sK2) != k1_funct_1(k8_relat_1(sK3,sK4),sK2) | spl5_7),
% 0.19/0.45    inference(avatar_component_clause,[],[f75])).
% 0.19/0.45  fof(f160,plain,(
% 0.19/0.45    ~spl5_8 | ~spl5_6 | spl5_20 | ~spl5_11),
% 0.19/0.45    inference(avatar_split_clause,[],[f155,f108,f158,f69,f81])).
% 0.19/0.45  fof(f81,plain,(
% 0.19/0.45    spl5_8 <=> v1_relat_1(sK4)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.19/0.45  fof(f69,plain,(
% 0.19/0.45    spl5_6 <=> v1_funct_1(sK4)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.19/0.45  fof(f108,plain,(
% 0.19/0.45    spl5_11 <=> ! [X1,X0] : (k1_xboole_0 = k1_funct_1(k8_relat_1(X0,sK4),X1) | ~v1_relat_1(k8_relat_1(X0,sK4)) | k1_funct_1(k8_relat_1(X0,sK4),X1) = k1_funct_1(sK4,X1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.19/0.45  fof(f155,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k1_xboole_0 = k1_funct_1(k8_relat_1(X0,sK4),X1) | k1_funct_1(k8_relat_1(X0,sK4),X1) = k1_funct_1(sK4,X1) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) ) | ~spl5_11),
% 0.19/0.45    inference(resolution,[],[f109,f37])).
% 0.19/0.45  fof(f37,plain,(
% 0.19/0.45    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f15])).
% 0.19/0.45  fof(f15,plain,(
% 0.19/0.45    ! [X0,X1] : ((v1_funct_1(k8_relat_1(X0,X1)) & v1_relat_1(k8_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.45    inference(flattening,[],[f14])).
% 0.19/0.45  fof(f14,plain,(
% 0.19/0.45    ! [X0,X1] : ((v1_funct_1(k8_relat_1(X0,X1)) & v1_relat_1(k8_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.45    inference(ennf_transformation,[],[f2])).
% 0.19/0.45  fof(f2,axiom,(
% 0.19/0.45    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v1_funct_1(k8_relat_1(X0,X1)) & v1_relat_1(k8_relat_1(X0,X1))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_funct_1)).
% 0.19/0.45  fof(f109,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~v1_relat_1(k8_relat_1(X0,sK4)) | k1_xboole_0 = k1_funct_1(k8_relat_1(X0,sK4),X1) | k1_funct_1(k8_relat_1(X0,sK4),X1) = k1_funct_1(sK4,X1)) ) | ~spl5_11),
% 0.19/0.45    inference(avatar_component_clause,[],[f108])).
% 0.19/0.45  fof(f127,plain,(
% 0.19/0.45    ~spl5_8 | ~spl5_6 | spl5_14 | ~spl5_12),
% 0.19/0.45    inference(avatar_split_clause,[],[f117,f113,f125,f69,f81])).
% 0.19/0.45  fof(f113,plain,(
% 0.19/0.45    spl5_12 <=> ! [X1,X0] : (~r2_hidden(k1_funct_1(sK4,X0),X1) | k1_funct_1(sK4,X0) = k1_funct_1(k8_relat_1(X1,sK4),X0) | ~r2_hidden(X0,k1_relat_1(sK4)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.19/0.45  fof(f117,plain,(
% 0.19/0.45    ( ! [X4,X3] : (k1_funct_1(sK4,X3) = k1_funct_1(k8_relat_1(X4,sK4),X3) | ~r2_hidden(k1_funct_1(sK4,X3),X4) | k1_xboole_0 = k1_funct_1(sK4,X3) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) ) | ~spl5_12),
% 0.19/0.45    inference(resolution,[],[f114,f45])).
% 0.19/0.45  fof(f45,plain,(
% 0.19/0.45    ( ! [X0,X1] : (r2_hidden(X1,k1_relat_1(X0)) | k1_funct_1(X0,X1) = k1_xboole_0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.45    inference(equality_resolution,[],[f36])).
% 0.19/0.45  fof(f36,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f24])).
% 0.19/0.45  fof(f24,plain,(
% 0.19/0.45    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.45    inference(nnf_transformation,[],[f13])).
% 0.19/0.45  fof(f13,plain,(
% 0.19/0.45    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.45    inference(flattening,[],[f12])).
% 0.19/0.45  fof(f12,plain,(
% 0.19/0.45    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.45    inference(ennf_transformation,[],[f1])).
% 0.19/0.45  fof(f1,axiom,(
% 0.19/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 0.19/0.45  fof(f114,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK4)) | k1_funct_1(sK4,X0) = k1_funct_1(k8_relat_1(X1,sK4),X0) | ~r2_hidden(k1_funct_1(sK4,X0),X1)) ) | ~spl5_12),
% 0.19/0.45    inference(avatar_component_clause,[],[f113])).
% 0.19/0.45  fof(f115,plain,(
% 0.19/0.45    ~spl5_8 | ~spl5_6 | spl5_12 | ~spl5_10),
% 0.19/0.45    inference(avatar_split_clause,[],[f111,f97,f113,f69,f81])).
% 0.19/0.45  fof(f97,plain,(
% 0.19/0.45    spl5_10 <=> ! [X1,X0] : (~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4))) | k1_funct_1(sK4,X0) = k1_funct_1(k8_relat_1(X1,sK4),X0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.19/0.45  fof(f111,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~r2_hidden(k1_funct_1(sK4,X0),X1) | ~r2_hidden(X0,k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | k1_funct_1(sK4,X0) = k1_funct_1(k8_relat_1(X1,sK4),X0)) ) | ~spl5_10),
% 0.19/0.45    inference(resolution,[],[f43,f98])).
% 0.19/0.45  fof(f98,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4))) | k1_funct_1(sK4,X0) = k1_funct_1(k8_relat_1(X1,sK4),X0)) ) | ~spl5_10),
% 0.19/0.45    inference(avatar_component_clause,[],[f97])).
% 0.19/0.45  fof(f43,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | ~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f26])).
% 0.19/0.45  fof(f26,plain,(
% 0.19/0.45    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | ~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.19/0.45    inference(flattening,[],[f25])).
% 0.19/0.45  fof(f25,plain,(
% 0.19/0.45    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | (~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.19/0.45    inference(nnf_transformation,[],[f20])).
% 0.19/0.45  fof(f20,plain,(
% 0.19/0.45    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.19/0.45    inference(flattening,[],[f19])).
% 0.19/0.45  fof(f19,plain,(
% 0.19/0.45    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.19/0.45    inference(ennf_transformation,[],[f3])).
% 0.19/0.45  fof(f3,axiom,(
% 0.19/0.45    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_funct_1)).
% 0.19/0.45  fof(f110,plain,(
% 0.19/0.45    ~spl5_8 | ~spl5_6 | spl5_11 | ~spl5_10),
% 0.19/0.45    inference(avatar_split_clause,[],[f105,f97,f108,f69,f81])).
% 0.19/0.45  fof(f105,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k1_xboole_0 = k1_funct_1(k8_relat_1(X0,sK4),X1) | k1_funct_1(k8_relat_1(X0,sK4),X1) = k1_funct_1(sK4,X1) | ~v1_relat_1(k8_relat_1(X0,sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) ) | ~spl5_10),
% 0.19/0.45    inference(resolution,[],[f102,f38])).
% 0.19/0.45  fof(f38,plain,(
% 0.19/0.45    ( ! [X0,X1] : (v1_funct_1(k8_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f15])).
% 0.19/0.45  fof(f102,plain,(
% 0.19/0.45    ( ! [X4,X3] : (~v1_funct_1(k8_relat_1(X4,sK4)) | k1_xboole_0 = k1_funct_1(k8_relat_1(X4,sK4),X3) | k1_funct_1(sK4,X3) = k1_funct_1(k8_relat_1(X4,sK4),X3) | ~v1_relat_1(k8_relat_1(X4,sK4))) ) | ~spl5_10),
% 0.19/0.45    inference(resolution,[],[f98,f45])).
% 0.19/0.45  fof(f99,plain,(
% 0.19/0.45    ~spl5_8 | spl5_10 | ~spl5_6),
% 0.19/0.45    inference(avatar_split_clause,[],[f94,f69,f97,f81])).
% 0.19/0.45  fof(f94,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4))) | k1_funct_1(sK4,X0) = k1_funct_1(k8_relat_1(X1,sK4),X0) | ~v1_relat_1(sK4)) ) | ~spl5_6),
% 0.19/0.45    inference(resolution,[],[f40,f70])).
% 0.19/0.45  fof(f70,plain,(
% 0.19/0.45    v1_funct_1(sK4) | ~spl5_6),
% 0.19/0.45    inference(avatar_component_clause,[],[f69])).
% 0.19/0.45  fof(f40,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f18])).
% 0.19/0.45  fof(f18,plain,(
% 0.19/0.45    ! [X0,X1,X2] : (k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.19/0.45    inference(flattening,[],[f17])).
% 0.19/0.45  fof(f17,plain,(
% 0.19/0.45    ! [X0,X1,X2] : ((k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.19/0.45    inference(ennf_transformation,[],[f4])).
% 0.19/0.45  fof(f4,axiom,(
% 0.19/0.45    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_1)).
% 0.19/0.45  fof(f90,plain,(
% 0.19/0.45    ~spl5_5 | spl5_8),
% 0.19/0.45    inference(avatar_contradiction_clause,[],[f89])).
% 0.19/0.45  fof(f89,plain,(
% 0.19/0.45    $false | (~spl5_5 | spl5_8)),
% 0.19/0.45    inference(subsumption_resolution,[],[f66,f88])).
% 0.19/0.45  fof(f88,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_8),
% 0.19/0.45    inference(resolution,[],[f82,f39])).
% 0.19/0.45  fof(f39,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f16])).
% 0.19/0.45  fof(f16,plain,(
% 0.19/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.45    inference(ennf_transformation,[],[f5])).
% 0.19/0.45  fof(f5,axiom,(
% 0.19/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.45  fof(f82,plain,(
% 0.19/0.45    ~v1_relat_1(sK4) | spl5_8),
% 0.19/0.45    inference(avatar_component_clause,[],[f81])).
% 0.19/0.45  fof(f66,plain,(
% 0.19/0.45    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_5),
% 0.19/0.45    inference(avatar_component_clause,[],[f65])).
% 0.19/0.45  fof(f65,plain,(
% 0.19/0.45    spl5_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.19/0.45  fof(f77,plain,(
% 0.19/0.45    ~spl5_7 | spl5_1 | ~spl5_5),
% 0.19/0.45    inference(avatar_split_clause,[],[f73,f65,f49,f75])).
% 0.19/0.45  fof(f49,plain,(
% 0.19/0.45    spl5_1 <=> k1_funct_1(sK4,sK2) = k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.45  fof(f73,plain,(
% 0.19/0.45    k1_funct_1(sK4,sK2) != k1_funct_1(k8_relat_1(sK3,sK4),sK2) | (spl5_1 | ~spl5_5)),
% 0.19/0.45    inference(superposition,[],[f50,f72])).
% 0.19/0.45  fof(f72,plain,(
% 0.19/0.45    ( ! [X0] : (k6_relset_1(sK0,sK1,X0,sK4) = k8_relat_1(X0,sK4)) ) | ~spl5_5),
% 0.19/0.45    inference(resolution,[],[f44,f66])).
% 0.19/0.45  fof(f44,plain,(
% 0.19/0.45    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f21])).
% 0.19/0.45  fof(f21,plain,(
% 0.19/0.45    ! [X0,X1,X2,X3] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.45    inference(ennf_transformation,[],[f6])).
% 0.19/0.45  fof(f6,axiom,(
% 0.19/0.45    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).
% 0.19/0.45  fof(f50,plain,(
% 0.19/0.45    k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2) | spl5_1),
% 0.19/0.45    inference(avatar_component_clause,[],[f49])).
% 0.19/0.45  fof(f71,plain,(
% 0.19/0.45    spl5_6),
% 0.19/0.45    inference(avatar_split_clause,[],[f27,f69])).
% 0.19/0.45  fof(f27,plain,(
% 0.19/0.45    v1_funct_1(sK4)),
% 0.19/0.45    inference(cnf_transformation,[],[f23])).
% 0.19/0.45  fof(f23,plain,(
% 0.19/0.45    k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2) & k1_xboole_0 != sK1 & r2_hidden(k1_funct_1(sK4,sK2),sK3) & r2_hidden(sK2,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK4)),
% 0.19/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f11,f22])).
% 0.19/0.45  fof(f22,plain,(
% 0.19/0.45    ? [X0,X1,X2,X3,X4] : (k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2) & k1_xboole_0 != X1 & r2_hidden(k1_funct_1(X4,X2),X3) & r2_hidden(X2,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2) & k1_xboole_0 != sK1 & r2_hidden(k1_funct_1(sK4,sK2),sK3) & r2_hidden(sK2,sK0) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK4))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f11,plain,(
% 0.19/0.45    ? [X0,X1,X2,X3,X4] : (k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2) & k1_xboole_0 != X1 & r2_hidden(k1_funct_1(X4,X2),X3) & r2_hidden(X2,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4))),
% 0.19/0.45    inference(flattening,[],[f10])).
% 0.19/0.45  fof(f10,plain,(
% 0.19/0.45    ? [X0,X1,X2,X3,X4] : (((k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2) & k1_xboole_0 != X1) & (r2_hidden(k1_funct_1(X4,X2),X3) & r2_hidden(X2,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)))),
% 0.19/0.45    inference(ennf_transformation,[],[f9])).
% 0.19/0.45  fof(f9,plain,(
% 0.19/0.45    ~! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => ((r2_hidden(k1_funct_1(X4,X2),X3) & r2_hidden(X2,X0)) => (k1_funct_1(X4,X2) = k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2) | k1_xboole_0 = X1)))),
% 0.19/0.45    inference(pure_predicate_removal,[],[f8])).
% 0.19/0.46  fof(f8,negated_conjecture,(
% 0.19/0.46    ~! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) => ((r2_hidden(k1_funct_1(X4,X2),X3) & r2_hidden(X2,X0)) => (k1_funct_1(X4,X2) = k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2) | k1_xboole_0 = X1)))),
% 0.19/0.46    inference(negated_conjecture,[],[f7])).
% 0.19/0.46  fof(f7,conjecture,(
% 0.19/0.46    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) => ((r2_hidden(k1_funct_1(X4,X2),X3) & r2_hidden(X2,X0)) => (k1_funct_1(X4,X2) = k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2) | k1_xboole_0 = X1)))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_funct_2)).
% 0.19/0.46  fof(f67,plain,(
% 0.19/0.46    spl5_5),
% 0.19/0.46    inference(avatar_split_clause,[],[f28,f65])).
% 0.19/0.46  fof(f28,plain,(
% 0.19/0.46    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.46    inference(cnf_transformation,[],[f23])).
% 0.19/0.46  fof(f59,plain,(
% 0.19/0.46    spl5_3),
% 0.19/0.46    inference(avatar_split_clause,[],[f30,f57])).
% 0.19/0.46  fof(f30,plain,(
% 0.19/0.46    r2_hidden(k1_funct_1(sK4,sK2),sK3)),
% 0.19/0.46    inference(cnf_transformation,[],[f23])).
% 0.19/0.46  fof(f51,plain,(
% 0.19/0.46    ~spl5_1),
% 0.19/0.46    inference(avatar_split_clause,[],[f32,f49])).
% 0.19/0.46  fof(f32,plain,(
% 0.19/0.46    k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2)),
% 0.19/0.46    inference(cnf_transformation,[],[f23])).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (9569)------------------------------
% 0.19/0.46  % (9569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (9569)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (9569)Memory used [KB]: 10746
% 0.19/0.46  % (9569)Time elapsed: 0.020 s
% 0.19/0.46  % (9569)------------------------------
% 0.19/0.46  % (9569)------------------------------
% 0.19/0.46  % (9560)Success in time 0.106 s
%------------------------------------------------------------------------------
