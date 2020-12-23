%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t69_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:31 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   61 (  93 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :  127 ( 209 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f143,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f58,f65,f72,f79,f89,f98,f106,f126,f140])).

fof(f140,plain,
    ( spl3_1
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f138,f88])).

fof(f88,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f138,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f132,f50])).

fof(f50,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_1
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f132,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f127,f125])).

fof(f125,plain,
    ( k3_xboole_0(sK1,sK0) = sK1
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl3_16
  <=> k3_xboole_0(sK1,sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f127,plain,
    ( k3_xboole_0(sK1,sK0) = k1_xboole_0
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f78,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t69_xboole_1.p',d7_xboole_0)).

fof(f78,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_8
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f126,plain,
    ( spl3_16
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f118,f70,f124])).

fof(f70,plain,
    ( spl3_6
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f118,plain,
    ( k3_xboole_0(sK1,sK0) = sK1
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f71,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t69_xboole_1.p',t28_xboole_1)).

fof(f71,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f106,plain,
    ( spl3_14
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f99,f77,f104])).

fof(f104,plain,
    ( spl3_14
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f99,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f78,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t69_xboole_1.p',symmetry_r1_xboole_0)).

fof(f98,plain,
    ( spl3_12
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f80,f56,f96])).

fof(f96,plain,
    ( spl3_12
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f56,plain,
    ( spl3_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f80,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f57,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t69_xboole_1.p',t6_boole)).

fof(f57,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f89,plain,
    ( spl3_10
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f82,f56,f87])).

fof(f82,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f80,f57])).

fof(f79,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f33,f77])).

fof(f33,plain,(
    r1_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( r1_xboole_0(sK1,sK0)
    & r1_tarski(sK1,sK0)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( r1_xboole_0(X1,X0)
        & r1_tarski(X1,X0)
        & ~ v1_xboole_0(X1) )
   => ( r1_xboole_0(sK1,sK0)
      & r1_tarski(sK1,sK0)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X1,X0)
      & r1_tarski(X1,X0)
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X1,X0)
      & r1_tarski(X1,X0)
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ~ ( r1_xboole_0(X1,X0)
            & r1_tarski(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t69_xboole_1.p',t69_xboole_1)).

fof(f72,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f32,f70])).

fof(f32,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f44,f63])).

fof(f63,plain,
    ( spl3_5
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f44,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f29])).

fof(f29,plain,
    ( ? [X0] : ~ v1_xboole_0(X0)
   => ~ v1_xboole_0(sK2) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ? [X0] : ~ v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t69_xboole_1.p',rc2_xboole_0)).

fof(f58,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f34,f56])).

fof(f34,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t69_xboole_1.p',dt_o_0_0_xboole_0)).

fof(f51,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f31,f49])).

fof(f31,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
