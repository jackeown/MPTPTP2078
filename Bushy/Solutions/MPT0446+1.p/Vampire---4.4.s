%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t30_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:01 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   64 (  98 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :  144 ( 237 expanded)
%              Number of equality atoms :   12 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f387,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f98,f102,f106,f114,f122,f157,f331,f386])).

fof(f386,plain,
    ( spl12_9
    | ~ spl12_18
    | ~ spl12_26 ),
    inference(avatar_contradiction_clause,[],[f385])).

fof(f385,plain,
    ( $false
    | ~ spl12_9
    | ~ spl12_18
    | ~ spl12_26 ),
    inference(subsumption_resolution,[],[f381,f97])).

fof(f97,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl12_9
  <=> ~ r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f381,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl12_18
    | ~ spl12_26 ),
    inference(superposition,[],[f237,f156])).

fof(f156,plain,
    ( k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl12_26 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl12_26
  <=> k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_26])])).

fof(f237,plain,
    ( ! [X1] : r2_hidden(sK0,k2_xboole_0(k1_relat_1(sK2),X1))
    | ~ spl12_18 ),
    inference(resolution,[],[f145,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t30_relat_1.p',d3_xboole_0)).

fof(f145,plain,
    ( ! [X0] : sP4(sK0,X0,k1_relat_1(sK2))
    | ~ spl12_18 ),
    inference(resolution,[],[f121,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f121,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl12_18 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl12_18
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f331,plain,
    ( spl12_6
    | ~ spl12_14
    | ~ spl12_26 ),
    inference(avatar_split_clause,[],[f325,f155,f112,f329])).

fof(f329,plain,
    ( spl12_6
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f112,plain,
    ( spl12_14
  <=> r2_hidden(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f325,plain,
    ( r2_hidden(sK1,k3_relat_1(sK2))
    | ~ spl12_14
    | ~ spl12_26 ),
    inference(superposition,[],[f234,f156])).

fof(f234,plain,
    ( ! [X1] : r2_hidden(sK1,k2_xboole_0(X1,k2_relat_1(sK2)))
    | ~ spl12_14 ),
    inference(resolution,[],[f132,f67])).

fof(f132,plain,
    ( ! [X1] : sP4(sK1,k2_relat_1(sK2),X1)
    | ~ spl12_14 ),
    inference(resolution,[],[f113,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f113,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f112])).

fof(f157,plain,
    ( spl12_26
    | ~ spl12_0 ),
    inference(avatar_split_clause,[],[f76,f73,f155])).

fof(f73,plain,
    ( spl12_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_0])])).

fof(f76,plain,
    ( k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl12_0 ),
    inference(resolution,[],[f74,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t30_relat_1.p',d6_relat_1)).

fof(f74,plain,
    ( v1_relat_1(sK2)
    | ~ spl12_0 ),
    inference(avatar_component_clause,[],[f73])).

fof(f122,plain,
    ( spl12_18
    | ~ spl12_12 ),
    inference(avatar_split_clause,[],[f110,f104,f120])).

fof(f104,plain,
    ( spl12_12
  <=> sP6(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f110,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl12_12 ),
    inference(resolution,[],[f105,f69])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ sP6(X2,X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X2,X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t30_relat_1.p',d4_relat_1)).

fof(f105,plain,
    ( sP6(sK0,sK2)
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f104])).

fof(f114,plain,
    ( spl12_14
    | ~ spl12_10 ),
    inference(avatar_split_clause,[],[f108,f100,f112])).

fof(f100,plain,
    ( spl12_10
  <=> sP9(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f108,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl12_10 ),
    inference(resolution,[],[f101,f71])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ sP9(X2,X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ sP9(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t30_relat_1.p',d5_relat_1)).

fof(f101,plain,
    ( sP9(sK1,sK2)
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f106,plain,
    ( spl12_12
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f82,f78,f104])).

fof(f78,plain,
    ( spl12_2
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f82,plain,
    ( sP6(sK0,sK2)
    | ~ spl12_2 ),
    inference(resolution,[],[f79,f49])).

fof(f49,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | sP6(X2,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f79,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f102,plain,
    ( spl12_10
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f81,f78,f100])).

fof(f81,plain,
    ( sP9(sK1,sK2)
    | ~ spl12_2 ),
    inference(resolution,[],[f79,f55])).

fof(f55,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | sP9(X2,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f98,plain,
    ( ~ spl12_7
    | ~ spl12_9 ),
    inference(avatar_split_clause,[],[f35,f96,f93])).

fof(f93,plain,
    ( spl12_7
  <=> ~ r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f35,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(X2)) )
      & r2_hidden(k4_tarski(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(k4_tarski(X0,X1),X2)
         => ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t30_relat_1.p',t30_relat_1)).

fof(f80,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f37,f78])).

fof(f37,plain,(
    r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    spl12_0 ),
    inference(avatar_split_clause,[],[f36,f73])).

fof(f36,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
