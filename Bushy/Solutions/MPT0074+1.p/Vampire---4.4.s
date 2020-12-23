%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t67_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:31 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 (  65 expanded)
%              Number of leaves         :   10 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   96 ( 164 expanded)
%              Number of equality atoms :   16 (  31 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f47,f51,f55,f69,f83,f96])).

fof(f96,plain,
    ( spl3_7
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f91,f54])).

fof(f54,plain,
    ( k1_xboole_0 != sK0
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_7
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f91,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_14 ),
    inference(resolution,[],[f82,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t67_xboole_1.p',t3_xboole_1)).

fof(f82,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_14
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f83,plain,
    ( spl3_14
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f79,f67,f45,f41,f81])).

fof(f41,plain,
    ( spl3_0
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f45,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f67,plain,
    ( spl3_10
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f79,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f77,f68])).

fof(f68,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f77,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_0
    | ~ spl3_2 ),
    inference(resolution,[],[f56,f46])).

fof(f46,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f56,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | r1_tarski(sK0,k3_xboole_0(sK1,X0)) )
    | ~ spl3_0 ),
    inference(resolution,[],[f42,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t67_xboole_1.p',t19_xboole_1)).

fof(f42,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f41])).

fof(f69,plain,
    ( spl3_10
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f59,f49,f67])).

fof(f49,plain,
    ( spl3_4
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f59,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f50,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k1_xboole_0 = k3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t67_xboole_1.p',d7_xboole_0)).

fof(f50,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f55,plain,(
    ~ spl3_7 ),
    inference(avatar_split_clause,[],[f31,f53])).

fof(f31,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X2)
          & r1_tarski(X0,X1) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t67_xboole_1.p',t67_xboole_1)).

fof(f51,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f30,f49])).

fof(f30,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f29,f45])).

fof(f29,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f28,f41])).

fof(f28,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
