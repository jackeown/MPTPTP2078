%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0616+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 (  96 expanded)
%              Number of leaves         :   11 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  168 ( 325 expanded)
%              Number of equality atoms :   27 (  55 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f36,f46,f59,f68,f73,f81,f85])).

fof(f85,plain,
    ( spl6_5
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f76,f41,f53])).

fof(f53,plain,
    ( spl6_5
  <=> sP4(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f41,plain,
    ( spl6_3
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f76,plain,
    ( sP4(sK0,sK2)
    | ~ spl6_3 ),
    inference(resolution,[],[f42,f15])).

fof(f15,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | sP4(X2,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f42,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f81,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f79,f74])).

fof(f74,plain,
    ( sK1 != k1_funct_1(sK2,sK0)
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f69,f42])).

fof(f69,plain,
    ( sK1 != k1_funct_1(sK2,sK0)
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f9,f62])).

fof(f62,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl6_5 ),
    inference(resolution,[],[f54,f25])).

fof(f25,plain,(
    ! [X2,X0] :
      ( ~ sP4(X2,X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X2,X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f54,plain,
    ( sP4(sK0,sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f9,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | sK1 != k1_funct_1(sK2,sK0)
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f79,plain,
    ( sK1 = k1_funct_1(sK2,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f78,f31])).

fof(f31,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl6_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f78,plain,
    ( ~ v1_relat_1(sK2)
    | sK1 = k1_funct_1(sK2,sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f77,f62])).

fof(f77,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | sK1 = k1_funct_1(sK2,sK0)
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f75,f35])).

fof(f35,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl6_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f75,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | sK1 = k1_funct_1(sK2,sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f42,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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

fof(f73,plain,
    ( sK1 != k1_funct_1(sK2,sK0)
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f68,plain,
    ( spl6_7
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f51,f44,f34,f30,f66])).

fof(f66,plain,
    ( spl6_7
  <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f44,plain,
    ( spl6_4
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f51,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f50,f31])).

fof(f50,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f48,f35])).

fof(f48,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl6_4 ),
    inference(resolution,[],[f45,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f45,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f59,plain,
    ( spl6_3
    | spl6_6 ),
    inference(avatar_split_clause,[],[f11,f57,f41])).

fof(f57,plain,
    ( spl6_6
  <=> sK1 = k1_funct_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f11,plain,
    ( sK1 = k1_funct_1(sK2,sK0)
    | r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f46,plain,
    ( spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f10,f44,f41])).

fof(f10,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f36,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f13,f34])).

fof(f13,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f32,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f12,f30])).

fof(f12,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f6])).

%------------------------------------------------------------------------------
