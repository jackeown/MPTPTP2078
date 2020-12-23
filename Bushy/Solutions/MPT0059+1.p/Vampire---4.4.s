%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t52_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:28 EDT 2019

% Result     : Theorem 16.78s
% Output     : Refutation 16.78s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 154 expanded)
%              Number of leaves         :   16 (  56 expanded)
%              Depth                    :    7
%              Number of atoms          :  227 ( 377 expanded)
%              Number of equality atoms :   20 (  50 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f797,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f181,f201,f282,f564,f618,f620,f622,f790,f792,f794,f796])).

fof(f796,plain,
    ( spl8_9
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f795])).

fof(f795,plain,
    ( $false
    | ~ spl8_9
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f611,f642])).

fof(f642,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2))
    | ~ spl8_9 ),
    inference(resolution,[],[f171,f79])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t52_xboole_1.p',d3_xboole_0)).

fof(f171,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl8_9
  <=> ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f611,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f610])).

fof(f610,plain,
    ( spl8_14
  <=> r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f794,plain,
    ( ~ spl8_10
    | spl8_15
    | ~ spl8_18 ),
    inference(avatar_contradiction_clause,[],[f793])).

fof(f793,plain,
    ( $false
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f783,f652])).

fof(f652,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | ~ spl8_10
    | ~ spl8_15 ),
    inference(resolution,[],[f608,f291])).

fof(f291,plain,
    ( ! [X4] :
        ( r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,X4))
        | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),X4) )
    | ~ spl8_10 ),
    inference(resolution,[],[f180,f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t52_xboole_1.p',d4_xboole_0)).

fof(f180,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl8_10
  <=> r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f608,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f607])).

fof(f607,plain,
    ( spl8_15
  <=> ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f783,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f782])).

fof(f782,plain,
    ( spl8_18
  <=> r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f792,plain,
    ( spl8_9
    | ~ spl8_10
    | spl8_21 ),
    inference(avatar_contradiction_clause,[],[f791])).

fof(f791,plain,
    ( $false
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f789,f662])).

fof(f662,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(resolution,[],[f641,f288])).

fof(f288,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK0,X1))
        | r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),X1) )
    | ~ spl8_10 ),
    inference(resolution,[],[f180,f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t52_xboole_1.p',d5_xboole_0)).

fof(f641,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1))
    | ~ spl8_9 ),
    inference(resolution,[],[f171,f80])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f789,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f788])).

fof(f788,plain,
    ( spl8_21
  <=> ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f790,plain,
    ( spl8_18
    | ~ spl8_21
    | spl8_13 ),
    inference(avatar_split_clause,[],[f630,f199,f788,f782])).

fof(f199,plain,
    ( spl8_13
  <=> ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f630,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | ~ spl8_13 ),
    inference(resolution,[],[f200,f73])).

fof(f200,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK2))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f199])).

fof(f622,plain,
    ( ~ spl8_12
    | ~ spl8_16 ),
    inference(avatar_contradiction_clause,[],[f621])).

fof(f621,plain,
    ( $false
    | ~ spl8_12
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f617,f319])).

fof(f319,plain,
    ( ! [X2] : ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(X2,sK1))
    | ~ spl8_12 ),
    inference(resolution,[],[f294,f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f294,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | ~ spl8_12 ),
    inference(resolution,[],[f197,f75])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f197,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK2))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl8_12
  <=> r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f617,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f616])).

fof(f616,plain,
    ( spl8_16
  <=> r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f620,plain,
    ( ~ spl8_12
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f619])).

fof(f619,plain,
    ( $false
    | ~ spl8_12
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f611,f327])).

fof(f327,plain,
    ( ! [X3] : ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(X3,sK2))
    | ~ spl8_12 ),
    inference(resolution,[],[f295,f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f295,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | ~ spl8_12 ),
    inference(resolution,[],[f197,f74])).

fof(f618,plain,
    ( spl8_14
    | spl8_16
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f182,f173,f616,f610])).

fof(f173,plain,
    ( spl8_8
  <=> r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f182,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2))
    | ~ spl8_8 ),
    inference(resolution,[],[f174,f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f174,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f173])).

fof(f564,plain,
    ( spl8_12
    | ~ spl8_11
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f194,f173,f176,f196])).

fof(f176,plain,
    ( spl8_11
  <=> ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f194,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK2))
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f193,f83])).

fof(f83,plain,(
    ~ sQ7_eqProxy(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    inference(equality_proxy_replacement,[],[f33,f82])).

fof(f82,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f33,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t52_xboole_1.p',t52_xboole_1)).

fof(f193,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK2))
    | sQ7_eqProxy(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | ~ spl8_8 ),
    inference(resolution,[],[f174,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | sQ7_eqProxy(k4_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f53,f82])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f282,plain,
    ( ~ spl8_8
    | spl8_11 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | ~ spl8_8
    | ~ spl8_11 ),
    inference(unit_resulting_resolution,[],[f213,f174,f215,f81])).

fof(f215,plain,
    ( ! [X4] : ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,X4))
    | ~ spl8_11 ),
    inference(resolution,[],[f177,f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f177,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f176])).

fof(f213,plain,
    ( ! [X2] : ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK0,X2))
    | ~ spl8_11 ),
    inference(resolution,[],[f177,f75])).

fof(f201,plain,
    ( spl8_8
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f109,f199,f173])).

fof(f109,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK2))
    | r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f83,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | sQ7_eqProxy(k4_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f55,f82])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f181,plain,
    ( spl8_8
    | spl8_10 ),
    inference(avatar_split_clause,[],[f108,f179,f173])).

fof(f108,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | r2_hidden(sK4(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f83,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | sQ7_eqProxy(k4_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f54,f82])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
