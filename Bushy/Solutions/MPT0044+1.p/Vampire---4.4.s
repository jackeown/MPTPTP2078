%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t37_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:26 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 (  52 expanded)
%              Number of leaves         :   11 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   82 ( 120 expanded)
%              Number of equality atoms :   27 (  45 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f47,f61,f62,f67,f70])).

fof(f70,plain,
    ( ~ spl2_4
    | spl2_7 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f68,f54])).

fof(f54,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_4
  <=> k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f68,plain,
    ( k4_xboole_0(sK0,sK1) != k1_xboole_0
    | ~ spl2_7 ),
    inference(resolution,[],[f57,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t37_xboole_1.p',l32_xboole_1)).

fof(f57,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl2_7
  <=> ~ r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f67,plain,
    ( spl2_5
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f64,f51])).

fof(f51,plain,
    ( k4_xboole_0(sK0,sK1) != k1_xboole_0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_5
  <=> k4_xboole_0(sK0,sK1) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f64,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0
    | ~ spl2_6 ),
    inference(resolution,[],[f31,f60])).

fof(f60,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_6
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,
    ( ~ spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f24,f56,f50])).

fof(f24,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k4_xboole_0(sK0,sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ r1_tarski(sK0,sK1)
      | k4_xboole_0(sK0,sK1) != k1_xboole_0 )
    & ( r1_tarski(sK0,sK1)
      | k4_xboole_0(sK0,sK1) = k1_xboole_0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_tarski(X0,X1)
          | k4_xboole_0(X0,X1) != k1_xboole_0 )
        & ( r1_tarski(X0,X1)
          | k4_xboole_0(X0,X1) = k1_xboole_0 ) )
   => ( ( ~ r1_tarski(sK0,sK1)
        | k4_xboole_0(sK0,sK1) != k1_xboole_0 )
      & ( r1_tarski(sK0,sK1)
        | k4_xboole_0(sK0,sK1) = k1_xboole_0 ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <~> r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
      <=> r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t37_xboole_1.p',t37_xboole_1)).

fof(f61,plain,
    ( spl2_4
    | spl2_6 ),
    inference(avatar_split_clause,[],[f23,f59,f53])).

fof(f23,plain,
    ( r1_tarski(sK0,sK1)
    | k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f26,f45])).

fof(f45,plain,
    ( spl2_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f26,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t37_xboole_1.p',d2_xboole_0)).

fof(f40,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f33,f38])).

fof(f38,plain,
    ( spl2_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f25,f26])).

fof(f25,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t37_xboole_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
