%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_0__t4_xboole_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:19 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  69 expanded)
%              Number of leaves         :    9 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   95 ( 159 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f48,f49,f65,f67,f83])).

fof(f83,plain,
    ( ~ spl4_0
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f80,f51])).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[],[f22,f50])).

fof(f50,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(resolution,[],[f23,f22])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_0__t4_xboole_0.p',l13_xboole_0)).

fof(f22,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_0__t4_xboole_0.p',dt_o_0_0_xboole_0)).

fof(f80,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_0
    | ~ spl4_4 ),
    inference(superposition,[],[f70,f77])).

fof(f77,plain,
    ( k3_xboole_0(sK0,sK1) = k1_xboole_0
    | ~ spl4_0 ),
    inference(resolution,[],[f31,f37])).

fof(f37,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl4_0
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_0__t4_xboole_0.p',d7_xboole_0)).

fof(f70,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f47,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_0__t4_xboole_0.p',d1_xboole_0)).

fof(f47,plain,
    ( r2_hidden(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl4_4
  <=> r2_hidden(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f67,plain,
    ( ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f47,f40])).

fof(f40,plain,
    ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK0,sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl4_2
  <=> ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f65,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f62,f57])).

fof(f57,plain,
    ( k3_xboole_0(sK0,sK1) = k1_xboole_0
    | ~ spl4_2 ),
    inference(resolution,[],[f53,f40])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f24,f23])).

fof(f24,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f62,plain,
    ( k3_xboole_0(sK0,sK1) != k1_xboole_0
    | ~ spl4_1 ),
    inference(resolution,[],[f30,f34])).

fof(f34,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl4_1
  <=> ~ r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f49,plain,
    ( spl4_4
    | spl4_2 ),
    inference(avatar_split_clause,[],[f19,f39,f46])).

fof(f19,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k3_xboole_0(sK0,sK1))
      | r2_hidden(sK2,k3_xboole_0(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
        & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
        & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_0__t4_xboole_0.p',t4_xboole_0)).

fof(f48,plain,
    ( spl4_4
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f21,f33,f46])).

fof(f21,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | r2_hidden(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,
    ( spl4_0
    | spl4_2 ),
    inference(avatar_split_clause,[],[f20,f39,f36])).

fof(f20,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k3_xboole_0(sK0,sK1))
      | r1_xboole_0(sK0,sK1) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
