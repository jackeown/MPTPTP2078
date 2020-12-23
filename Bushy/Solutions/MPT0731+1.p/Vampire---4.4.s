%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t14_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:24 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   27 (  30 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  41 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f64,f71,f74])).

fof(f74,plain,(
    ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f72,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t14_ordinal1.p',antisymmetry_r2_hidden)).

fof(f72,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl2_4 ),
    inference(superposition,[],[f38,f70])).

fof(f70,plain,
    ( k1_ordinal1(sK0) = sK0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl2_4
  <=> k1_ordinal1(sK0) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f38,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t14_ordinal1.p',t10_ordinal1)).

fof(f71,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f35,f69])).

fof(f35,plain,(
    k1_ordinal1(sK0) = sK0 ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    k1_ordinal1(sK0) = sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f31])).

fof(f31,plain,
    ( ? [X0] : k1_ordinal1(X0) = X0
   => k1_ordinal1(sK0) = sK0 ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] : k1_ordinal1(X0) = X0 ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t14_ordinal1.p',t14_ordinal1)).

fof(f64,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f37,f62])).

fof(f62,plain,
    ( spl2_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f37,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t14_ordinal1.p',d2_xboole_0)).

fof(f57,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f50,f55])).

fof(f55,plain,
    ( spl2_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f36,f37])).

fof(f36,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t14_ordinal1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
