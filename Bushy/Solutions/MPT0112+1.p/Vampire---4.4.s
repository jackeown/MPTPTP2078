%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t105_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:20 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   40 (  52 expanded)
%              Number of leaves         :   12 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 (  95 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f55,f62,f69,f78,f83])).

fof(f83,plain,
    ( ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f81,f68])).

fof(f68,plain,
    ( k4_xboole_0(sK1,sK0) = k1_xboole_0
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_6
  <=> k4_xboole_0(sK1,sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f81,plain,
    ( k4_xboole_0(sK1,sK0) != k1_xboole_0
    | ~ spl2_2 ),
    inference(resolution,[],[f80,f54])).

fof(f54,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_2
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(resolution,[],[f38,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t105_xboole_1.p',t60_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t105_xboole_1.p',l32_xboole_1)).

fof(f78,plain,
    ( ~ spl2_9
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f71,f53,f76])).

fof(f76,plain,
    ( spl2_9
  <=> ~ r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f71,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f37,f54])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t105_xboole_1.p',antisymmetry_r2_xboole_0)).

fof(f69,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f30,f67])).

fof(f30,plain,(
    k4_xboole_0(sK1,sK0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k4_xboole_0(sK1,sK0) = k1_xboole_0
    & r2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( k4_xboole_0(X1,X0) = k1_xboole_0
        & r2_xboole_0(X0,X1) )
   => ( k4_xboole_0(sK1,sK0) = k1_xboole_0
      & r2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X1,X0) = k1_xboole_0
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k4_xboole_0(X1,X0) = k1_xboole_0
          & r2_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ~ ( k4_xboole_0(X1,X0) = k1_xboole_0
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t105_xboole_1.p',t105_xboole_1)).

fof(f62,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f32,f60])).

fof(f60,plain,
    ( spl2_4
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f32,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t105_xboole_1.p',d2_xboole_0)).

fof(f55,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f29,f53])).

fof(f29,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f41,f46])).

fof(f46,plain,
    ( spl2_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f31,f32])).

fof(f31,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t105_xboole_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
