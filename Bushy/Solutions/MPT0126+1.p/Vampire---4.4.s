%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t42_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:59 EDT 2019

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :  201 ( 437 expanded)
%              Number of leaves         :   36 ( 151 expanded)
%              Depth                    :    8
%              Number of atoms          :  529 (1136 expanded)
%              Number of equality atoms :   94 ( 308 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f591,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f122,f129,f144,f151,f159,f185,f228,f253,f276,f281,f298,f303,f315,f337,f344,f358,f359,f364,f378,f381,f386,f400,f405,f410,f428,f449,f453,f476,f491,f516,f531,f565,f569,f590])).

fof(f590,plain,
    ( spl8_7
    | ~ spl8_18 ),
    inference(avatar_contradiction_clause,[],[f589])).

fof(f589,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f574,f67])).

fof(f67,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t42_enumset1.p',d1_tarski)).

fof(f574,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl8_7
    | ~ spl8_18 ),
    inference(backward_demodulation,[],[f263,f147])).

fof(f147,plain,
    ( ~ r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k1_tarski(sK0))
    | ~ spl8_7 ),
    inference(resolution,[],[f137,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t42_enumset1.p',d3_xboole_0)).

fof(f137,plain,
    ( ~ r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl8_7
  <=> ~ r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f263,plain,
    ( sK0 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl8_18
  <=> sK0 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f569,plain,
    ( spl8_7
    | ~ spl8_22 ),
    inference(avatar_contradiction_clause,[],[f568])).

fof(f568,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f567,f63])).

fof(f63,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_tarski(X3,X1)) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t42_enumset1.p',d2_tarski)).

fof(f567,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | ~ spl8_7
    | ~ spl8_22 ),
    inference(forward_demodulation,[],[f148,f275])).

fof(f275,plain,
    ( sK1 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl8_22
  <=> sK1 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f148,plain,
    ( ~ r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k2_tarski(sK1,sK2))
    | ~ spl8_7 ),
    inference(resolution,[],[f137,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f565,plain,
    ( spl8_13
    | ~ spl8_22 ),
    inference(avatar_contradiction_clause,[],[f564])).

fof(f564,plain,
    ( $false
    | ~ spl8_13
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f563,f63])).

fof(f563,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | ~ spl8_13
    | ~ spl8_22 ),
    inference(forward_demodulation,[],[f184,f275])).

fof(f184,plain,
    ( ~ r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k2_tarski(sK1,sK2))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl8_13
  <=> ~ r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f531,plain,
    ( spl8_9
    | ~ spl8_22 ),
    inference(avatar_contradiction_clause,[],[f530])).

fof(f530,plain,
    ( $false
    | ~ spl8_9
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f521,f53])).

fof(f53,plain,(
    ! [X4,X2,X0] : r2_hidden(X4,k1_enumset1(X0,X4,X2)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X3] :
      ( r2_hidden(X4,X3)
      | k1_enumset1(X0,X4,X2) != X3 ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t42_enumset1.p',d1_enumset1)).

fof(f521,plain,
    ( ~ r2_hidden(sK1,k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_9
    | ~ spl8_22 ),
    inference(backward_demodulation,[],[f275,f143])).

fof(f143,plain,
    ( ~ r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl8_9
  <=> ~ r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f516,plain,
    ( spl8_9
    | ~ spl8_12
    | spl8_21 ),
    inference(avatar_contradiction_clause,[],[f515])).

fof(f515,plain,
    ( $false
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f514,f53])).

fof(f514,plain,
    ( ~ r2_hidden(sK1,k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f143,f408])).

fof(f408,plain,
    ( sK1 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_12
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f407,f266])).

fof(f266,plain,
    ( sK2 != sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl8_21
  <=> sK2 != sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f407,plain,
    ( sK2 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | sK1 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_12 ),
    inference(resolution,[],[f181,f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f181,plain,
    ( r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k2_tarski(sK1,sK2))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl8_12
  <=> r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f491,plain,
    ( spl8_9
    | spl8_41
    | spl8_43 ),
    inference(avatar_contradiction_clause,[],[f490])).

fof(f490,plain,
    ( $false
    | ~ spl8_9
    | ~ spl8_41
    | ~ spl8_43 ),
    inference(subsumption_resolution,[],[f480,f53])).

fof(f480,plain,
    ( ~ r2_hidden(sK1,k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_9
    | ~ spl8_41
    | ~ spl8_43 ),
    inference(backward_demodulation,[],[f403,f143])).

fof(f403,plain,
    ( sK1 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_41
    | ~ spl8_43 ),
    inference(subsumption_resolution,[],[f402,f393])).

fof(f393,plain,
    ( ~ r2_hidden(sK7(sK1,sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),sK1)
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f392])).

fof(f392,plain,
    ( spl8_41
  <=> ~ r2_hidden(sK7(sK1,sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f402,plain,
    ( r2_hidden(sK7(sK1,sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),sK1)
    | sK1 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_43 ),
    inference(resolution,[],[f399,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X1)
      | r2_hidden(sK7(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t42_enumset1.p',t2_tarski)).

fof(f399,plain,
    ( ~ r2_hidden(sK7(sK1,sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)))
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f398])).

fof(f398,plain,
    ( spl8_43
  <=> ~ r2_hidden(sK7(sK1,sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f476,plain,
    ( spl8_9
    | ~ spl8_18 ),
    inference(avatar_contradiction_clause,[],[f475])).

fof(f475,plain,
    ( $false
    | ~ spl8_9
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f474,f55])).

fof(f55,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k1_enumset1(X4,X1,X2)) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k1_enumset1(X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f474,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_9
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f143,f263])).

fof(f453,plain,
    ( spl8_7
    | ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f452])).

fof(f452,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f451,f61])).

fof(f61,plain,(
    ! [X0,X3] : r2_hidden(X3,k2_tarski(X0,X3)) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f451,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | ~ spl8_7
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f148,f269])).

fof(f269,plain,
    ( sK2 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl8_20
  <=> sK2 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f449,plain,
    ( spl8_13
    | ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f448])).

fof(f448,plain,
    ( $false
    | ~ spl8_13
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f447,f61])).

fof(f447,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | ~ spl8_13
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f184,f269])).

fof(f428,plain,
    ( spl8_9
    | ~ spl8_12
    | spl8_23 ),
    inference(avatar_contradiction_clause,[],[f427])).

fof(f427,plain,
    ( $false
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f413,f51])).

fof(f51,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k1_enumset1(X0,X1,X4)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f413,plain,
    ( ~ r2_hidden(sK2,k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_23 ),
    inference(backward_demodulation,[],[f411,f143])).

fof(f411,plain,
    ( sK2 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_12
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f407,f272])).

fof(f272,plain,
    ( sK1 != sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl8_23
  <=> sK1 != sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f410,plain,
    ( ~ spl8_12
    | spl8_21
    | spl8_23 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | ~ spl8_12
    | ~ spl8_21
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f408,f272])).

fof(f405,plain,
    ( spl8_23
    | spl8_41
    | spl8_43 ),
    inference(avatar_contradiction_clause,[],[f404])).

fof(f404,plain,
    ( $false
    | ~ spl8_23
    | ~ spl8_41
    | ~ spl8_43 ),
    inference(subsumption_resolution,[],[f403,f272])).

fof(f400,plain,
    ( ~ spl8_41
    | ~ spl8_43
    | spl8_23 ),
    inference(avatar_split_clause,[],[f339,f271,f398,f392])).

fof(f339,plain,
    ( ~ r2_hidden(sK7(sK1,sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)))
    | ~ r2_hidden(sK7(sK1,sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),sK1)
    | ~ spl8_23 ),
    inference(extensionality_resolution,[],[f46,f272])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | ~ r2_hidden(sK7(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f386,plain,
    ( spl8_19
    | spl8_37
    | spl8_39 ),
    inference(avatar_contradiction_clause,[],[f385])).

fof(f385,plain,
    ( $false
    | ~ spl8_19
    | ~ spl8_37
    | ~ spl8_39 ),
    inference(subsumption_resolution,[],[f384,f260])).

fof(f260,plain,
    ( sK0 != sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl8_19
  <=> sK0 != sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f384,plain,
    ( sK0 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_37
    | ~ spl8_39 ),
    inference(subsumption_resolution,[],[f383,f377])).

fof(f377,plain,
    ( ~ r2_hidden(sK7(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),sK0),sK0)
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f376])).

fof(f376,plain,
    ( spl8_39
  <=> ~ r2_hidden(sK7(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f383,plain,
    ( r2_hidden(sK7(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),sK0),sK0)
    | sK0 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_37 ),
    inference(resolution,[],[f371,f45])).

fof(f371,plain,
    ( ~ r2_hidden(sK7(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),sK0),sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)))
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f370])).

fof(f370,plain,
    ( spl8_37
  <=> ~ r2_hidden(sK7(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),sK0),sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f381,plain,
    ( ~ spl8_10
    | spl8_19 ),
    inference(avatar_contradiction_clause,[],[f380])).

fof(f380,plain,
    ( $false
    | ~ spl8_10
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f379,f260])).

fof(f379,plain,
    ( sK0 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_10 ),
    inference(resolution,[],[f155,f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f155,plain,
    ( r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k1_tarski(sK0))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl8_10
  <=> r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f378,plain,
    ( ~ spl8_37
    | ~ spl8_39
    | spl8_19 ),
    inference(avatar_split_clause,[],[f319,f259,f376,f370])).

fof(f319,plain,
    ( ~ r2_hidden(sK7(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),sK0),sK0)
    | ~ r2_hidden(sK7(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),sK0),sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)))
    | ~ spl8_19 ),
    inference(extensionality_resolution,[],[f46,f260])).

fof(f364,plain,
    ( spl8_21
    | spl8_33
    | spl8_35 ),
    inference(avatar_contradiction_clause,[],[f363])).

fof(f363,plain,
    ( $false
    | ~ spl8_21
    | ~ spl8_33
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f362,f266])).

fof(f362,plain,
    ( sK2 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_33
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f361,f357])).

fof(f357,plain,
    ( ~ r2_hidden(sK7(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),sK2),sK2)
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f356])).

fof(f356,plain,
    ( spl8_35
  <=> ~ r2_hidden(sK7(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f361,plain,
    ( r2_hidden(sK7(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),sK2),sK2)
    | sK2 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_33 ),
    inference(resolution,[],[f351,f45])).

fof(f351,plain,
    ( ~ r2_hidden(sK7(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),sK2),sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)))
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl8_33
  <=> ~ r2_hidden(sK7(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),sK2),sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f359,plain,
    ( spl8_10
    | ~ spl8_6
    | spl8_13 ),
    inference(avatar_split_clause,[],[f279,f183,f133,f154])).

fof(f133,plain,
    ( spl8_6
  <=> r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f279,plain,
    ( r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k1_tarski(sK0))
    | ~ spl8_6
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f278,f184])).

fof(f278,plain,
    ( r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k2_tarski(sK1,sK2))
    | r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k1_tarski(sK0))
    | ~ spl8_6 ),
    inference(resolution,[],[f134,f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f134,plain,
    ( r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f358,plain,
    ( ~ spl8_33
    | ~ spl8_35
    | spl8_21 ),
    inference(avatar_split_clause,[],[f285,f265,f356,f350])).

fof(f285,plain,
    ( ~ r2_hidden(sK7(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),sK2),sK2)
    | ~ r2_hidden(sK7(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),sK2),sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)))
    | ~ spl8_21 ),
    inference(extensionality_resolution,[],[f46,f266])).

fof(f344,plain,
    ( spl8_21
    | spl8_29
    | spl8_31 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | ~ spl8_21
    | ~ spl8_29
    | ~ spl8_31 ),
    inference(subsumption_resolution,[],[f342,f266])).

fof(f342,plain,
    ( sK2 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_29
    | ~ spl8_31 ),
    inference(subsumption_resolution,[],[f341,f330])).

fof(f330,plain,
    ( ~ r2_hidden(sK7(sK2,sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),sK2)
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl8_29
  <=> ~ r2_hidden(sK7(sK2,sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f341,plain,
    ( r2_hidden(sK7(sK2,sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),sK2)
    | sK2 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_31 ),
    inference(resolution,[],[f336,f45])).

fof(f336,plain,
    ( ~ r2_hidden(sK7(sK2,sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)))
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f335])).

fof(f335,plain,
    ( spl8_31
  <=> ~ r2_hidden(sK7(sK2,sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f337,plain,
    ( ~ spl8_29
    | ~ spl8_31
    | spl8_21 ),
    inference(avatar_split_clause,[],[f284,f265,f335,f329])).

fof(f284,plain,
    ( ~ r2_hidden(sK7(sK2,sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)))
    | ~ r2_hidden(sK7(sK2,sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),sK2)
    | ~ spl8_21 ),
    inference(extensionality_resolution,[],[f46,f266])).

fof(f315,plain,
    ( spl8_9
    | spl8_25
    | spl8_27 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | ~ spl8_9
    | ~ spl8_25
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f305,f55])).

fof(f305,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_9
    | ~ spl8_25
    | ~ spl8_27 ),
    inference(backward_demodulation,[],[f301,f143])).

fof(f301,plain,
    ( sK0 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_25
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f300,f291])).

fof(f291,plain,
    ( ~ r2_hidden(sK7(sK0,sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),sK0)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl8_25
  <=> ~ r2_hidden(sK7(sK0,sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f300,plain,
    ( r2_hidden(sK7(sK0,sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),sK0)
    | sK0 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_27 ),
    inference(resolution,[],[f297,f45])).

fof(f297,plain,
    ( ~ r2_hidden(sK7(sK0,sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)))
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl8_27
  <=> ~ r2_hidden(sK7(sK0,sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f303,plain,
    ( spl8_19
    | spl8_25
    | spl8_27 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | ~ spl8_19
    | ~ spl8_25
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f301,f260])).

fof(f298,plain,
    ( ~ spl8_25
    | ~ spl8_27
    | spl8_19 ),
    inference(avatar_split_clause,[],[f282,f259,f296,f290])).

fof(f282,plain,
    ( ~ r2_hidden(sK7(sK0,sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)))
    | ~ r2_hidden(sK7(sK0,sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),sK0)
    | ~ spl8_19 ),
    inference(extensionality_resolution,[],[f46,f260])).

fof(f281,plain,
    ( ~ spl8_6
    | spl8_11
    | spl8_13 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_11
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f279,f158])).

fof(f158,plain,
    ( ~ r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k1_tarski(sK0))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl8_11
  <=> ~ r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f276,plain,
    ( spl8_18
    | spl8_20
    | spl8_22
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f230,f139,f274,f268,f262])).

fof(f139,plain,
    ( spl8_8
  <=> r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f230,plain,
    ( sK1 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | sK2 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_8 ),
    inference(resolution,[],[f140,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k1_enumset1(X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f140,plain,
    ( r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f253,plain,
    ( spl8_14
    | spl8_16
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f131,f117,f251,f245])).

fof(f245,plain,
    ( spl8_14
  <=> r2_hidden(sK7(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f251,plain,
    ( spl8_16
  <=> r2_hidden(sK7(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f117,plain,
    ( spl8_4
  <=> r2_hidden(sK7(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f131,plain,
    ( r2_hidden(sK7(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))),k2_tarski(sK1,sK2))
    | r2_hidden(sK7(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))),k1_tarski(sK0))
    | ~ spl8_4 ),
    inference(resolution,[],[f118,f59])).

fof(f118,plain,
    ( r2_hidden(sK7(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f228,plain,
    ( spl8_8
    | spl8_1
    | spl8_7 ),
    inference(avatar_split_clause,[],[f152,f136,f72,f139])).

fof(f72,plain,
    ( spl8_1
  <=> k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f152,plain,
    ( r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_1
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f146,f73])).

fof(f73,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f146,plain,
    ( r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl8_7 ),
    inference(resolution,[],[f137,f45])).

fof(f185,plain,
    ( ~ spl8_13
    | spl8_7 ),
    inference(avatar_split_clause,[],[f148,f136,f183])).

fof(f159,plain,
    ( ~ spl8_11
    | spl8_7 ),
    inference(avatar_split_clause,[],[f147,f136,f157])).

fof(f151,plain,
    ( spl8_1
    | spl8_7
    | spl8_9 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f149,f73])).

fof(f149,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f146,f143])).

fof(f144,plain,
    ( ~ spl8_7
    | ~ spl8_9
    | spl8_1 ),
    inference(avatar_split_clause,[],[f104,f72,f142,f136])).

fof(f104,plain,
    ( ~ r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ r2_hidden(sK7(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_enumset1(sK0,sK1,sK2)),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl8_1 ),
    inference(extensionality_resolution,[],[f46,f73])).

fof(f129,plain,
    ( spl8_1
    | spl8_3
    | spl8_5 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f127,f73])).

fof(f127,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f124,f115])).

fof(f115,plain,
    ( ~ r2_hidden(sK7(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl8_3
  <=> ~ r2_hidden(sK7(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))),k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f124,plain,
    ( r2_hidden(sK7(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))),k1_enumset1(sK0,sK1,sK2))
    | k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl8_5 ),
    inference(resolution,[],[f121,f45])).

fof(f121,plain,
    ( ~ r2_hidden(sK7(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl8_5
  <=> ~ r2_hidden(sK7(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f122,plain,
    ( ~ spl8_3
    | ~ spl8_5
    | spl8_1 ),
    inference(avatar_split_clause,[],[f103,f72,f120,f114])).

fof(f103,plain,
    ( ~ r2_hidden(sK7(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)))
    | ~ r2_hidden(sK7(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))),k1_enumset1(sK0,sK1,sK2))
    | ~ spl8_1 ),
    inference(extensionality_resolution,[],[f46,f73])).

fof(f74,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f20,f72])).

fof(f20,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t42_enumset1.p',t42_enumset1)).
%------------------------------------------------------------------------------
