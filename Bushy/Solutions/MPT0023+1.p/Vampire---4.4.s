%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t16_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:22 EDT 2019

% Result     : Theorem 11.38s
% Output     : Refutation 11.38s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 111 expanded)
%              Number of leaves         :    9 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  135 ( 270 expanded)
%              Number of equality atoms :   12 (  44 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f252,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f143,f144,f193,f201,f251])).

fof(f251,plain,
    ( spl6_9
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f249,f125])).

fof(f125,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl6_10
  <=> r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f249,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f244,f210])).

fof(f210,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | ~ spl6_12 ),
    inference(resolution,[],[f142,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t16_xboole_1.p',d4_xboole_0)).

fof(f142,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl6_12
  <=> r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f244,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(resolution,[],[f224,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f224,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f220,f209])).

fof(f209,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f142,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f220,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0)
    | ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | ~ spl6_9 ),
    inference(resolution,[],[f116,f46])).

fof(f116,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl6_9
  <=> ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f201,plain,
    ( ~ spl6_8
    | spl6_13 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f199,f183])).

fof(f183,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | ~ spl6_8 ),
    inference(resolution,[],[f128,f48])).

fof(f128,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | ~ spl6_8 ),
    inference(resolution,[],[f119,f47])).

fof(f119,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl6_8
  <=> r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f199,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f195,f127])).

fof(f127,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0)
    | ~ spl6_8 ),
    inference(resolution,[],[f119,f48])).

fof(f195,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0)
    | ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | ~ spl6_13 ),
    inference(resolution,[],[f139,f46])).

fof(f139,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl6_13
  <=> ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f193,plain,
    ( ~ spl6_8
    | spl6_11 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f184,f122])).

fof(f122,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl6_11
  <=> ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f184,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f128,f47])).

fof(f144,plain,
    ( ~ spl6_9
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f63,f138,f121,f115])).

fof(f63,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f50,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | sQ5_eqProxy(k3_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f38,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f50,plain,(
    ~ sQ5_eqProxy(k3_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(equality_proxy_replacement,[],[f23,f49])).

fof(f23,plain,(
    k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t16_xboole_1.p',t16_xboole_1)).

fof(f143,plain,
    ( spl6_8
    | spl6_12 ),
    inference(avatar_split_clause,[],[f64,f141,f118])).

fof(f64,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f50,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | sQ5_eqProxy(k3_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f39,f49])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f126,plain,
    ( spl6_8
    | spl6_10 ),
    inference(avatar_split_clause,[],[f65,f124,f118])).

fof(f65,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f50,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | sQ5_eqProxy(k3_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f40,f49])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
