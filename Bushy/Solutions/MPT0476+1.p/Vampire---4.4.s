%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t71_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:04 EDT 2019

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 222 expanded)
%              Number of leaves         :   12 (  63 expanded)
%              Depth                    :   17
%              Number of atoms          :  190 ( 643 expanded)
%              Number of equality atoms :   61 ( 216 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4818,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f89,f102,f582,f584,f4815,f4817])).

fof(f4817,plain,(
    spl9_7 ),
    inference(avatar_contradiction_clause,[],[f4816])).

fof(f4816,plain,
    ( $false
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f2663,f53])).

fof(f53,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t71_relat_1.p',d10_xboole_0)).

fof(f2663,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl9_7 ),
    inference(backward_demodulation,[],[f1791,f88])).

fof(f88,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(k6_relat_1(sK0)))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl9_7
  <=> ~ r1_tarski(sK0,k2_relat_1(k6_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f1791,plain,(
    ! [X1] : k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(subsumption_resolution,[],[f1789,f128])).

fof(f128,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK1(k6_relat_1(X2),X3),X3)
      | k2_relat_1(k6_relat_1(X2)) = X3
      | ~ r2_hidden(sK1(k6_relat_1(X2),X3),X2) ) ),
    inference(subsumption_resolution,[],[f126,f48])).

fof(f48,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t71_relat_1.p',dt_k6_relat_1)).

fof(f126,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK1(k6_relat_1(X2),X3),X3)
      | k2_relat_1(k6_relat_1(X2)) = X3
      | ~ r2_hidden(sK1(k6_relat_1(X2),X3),X2)
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(resolution,[],[f33,f56])).

fof(f56,plain,(
    ! [X0,X3] :
      ( r2_hidden(k4_tarski(X3,X3),k6_relat_1(X0))
      | ~ r2_hidden(X3,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(k4_tarski(X3,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | X2 != X3
      | r2_hidden(k4_tarski(X2,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t71_relat_1.p',d10_relat_1)).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
      | ~ r2_hidden(sK1(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t71_relat_1.p',d5_relat_1)).

fof(f1789,plain,(
    ! [X1] :
      ( r2_hidden(sK1(k6_relat_1(X1),X1),X1)
      | k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    inference(duplicate_literal_removal,[],[f1780])).

fof(f1780,plain,(
    ! [X1] :
      ( r2_hidden(sK1(k6_relat_1(X1),X1),X1)
      | r2_hidden(sK1(k6_relat_1(X1),X1),X1)
      | k2_relat_1(k6_relat_1(X1)) = X1
      | k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    inference(superposition,[],[f139,f845])).

fof(f845,plain,(
    ! [X0] :
      ( sK1(k6_relat_1(X0),X0) = sK3(k6_relat_1(X0),X0)
      | k2_relat_1(k6_relat_1(X0)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f836])).

fof(f836,plain,(
    ! [X0] :
      ( sK1(k6_relat_1(X0),X0) = sK3(k6_relat_1(X0),X0)
      | k2_relat_1(k6_relat_1(X0)) = X0
      | k2_relat_1(k6_relat_1(X0)) = X0
      | sK1(k6_relat_1(X0),X0) = sK3(k6_relat_1(X0),X0) ) ),
    inference(resolution,[],[f672,f140])).

fof(f140,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK1(k6_relat_1(X8),X9),X9)
      | k2_relat_1(k6_relat_1(X8)) = X9
      | sK1(k6_relat_1(X8),X9) = sK3(k6_relat_1(X8),X9) ) ),
    inference(subsumption_resolution,[],[f137,f48])).

fof(f137,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK1(k6_relat_1(X8),X9),X9)
      | k2_relat_1(k6_relat_1(X8)) = X9
      | sK1(k6_relat_1(X8),X9) = sK3(k6_relat_1(X8),X9)
      | ~ v1_relat_1(k6_relat_1(X8)) ) ),
    inference(resolution,[],[f32,f57])).

fof(f57,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0))
      | X2 = X3
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | X2 = X3
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK1(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f672,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK1(k6_relat_1(X1),X2),X1)
      | sK1(k6_relat_1(X1),X2) = sK3(k6_relat_1(X1),X2)
      | k2_relat_1(k6_relat_1(X1)) = X2 ) ),
    inference(duplicate_literal_removal,[],[f668])).

fof(f668,plain,(
    ! [X2,X1] :
      ( k2_relat_1(k6_relat_1(X1)) = X2
      | sK1(k6_relat_1(X1),X2) = sK3(k6_relat_1(X1),X2)
      | k2_relat_1(k6_relat_1(X1)) = X2
      | ~ r2_hidden(sK1(k6_relat_1(X1),X2),X1) ) ),
    inference(resolution,[],[f140,f128])).

fof(f139,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK3(k6_relat_1(X6),X7),X6)
      | r2_hidden(sK1(k6_relat_1(X6),X7),X7)
      | k2_relat_1(k6_relat_1(X6)) = X7 ) ),
    inference(subsumption_resolution,[],[f136,f48])).

fof(f136,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK1(k6_relat_1(X6),X7),X7)
      | k2_relat_1(k6_relat_1(X6)) = X7
      | r2_hidden(sK3(k6_relat_1(X6),X7),X6)
      | ~ v1_relat_1(k6_relat_1(X6)) ) ),
    inference(resolution,[],[f32,f58])).

fof(f58,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0))
      | r2_hidden(X2,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(X2,X0)
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4815,plain,(
    spl9_5 ),
    inference(avatar_contradiction_clause,[],[f4814])).

fof(f4814,plain,
    ( $false
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f2662,f53])).

fof(f2662,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl9_5 ),
    inference(backward_demodulation,[],[f1791,f82])).

fof(f82,plain,
    ( ~ r1_tarski(k2_relat_1(k6_relat_1(sK0)),sK0)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl9_5
  <=> ~ r1_tarski(k2_relat_1(k6_relat_1(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f584,plain,(
    spl9_11 ),
    inference(avatar_contradiction_clause,[],[f583])).

fof(f583,plain,
    ( $false
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f448,f53])).

fof(f448,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl9_11 ),
    inference(backward_demodulation,[],[f359,f101])).

fof(f101,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(k6_relat_1(sK0)))
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl9_11
  <=> ~ r1_tarski(sK0,k1_relat_1(k6_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f359,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(subsumption_resolution,[],[f356,f132])).

fof(f132,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK4(k6_relat_1(X2),X3),X3)
      | k1_relat_1(k6_relat_1(X2)) = X3
      | ~ r2_hidden(sK4(k6_relat_1(X2),X3),X2) ) ),
    inference(subsumption_resolution,[],[f130,f48])).

fof(f130,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK4(k6_relat_1(X2),X3),X3)
      | k1_relat_1(k6_relat_1(X2)) = X3
      | ~ r2_hidden(sK4(k6_relat_1(X2),X3),X2)
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(resolution,[],[f38,f56])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
      | ~ r2_hidden(sK4(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t71_relat_1.p',d4_relat_1)).

fof(f356,plain,(
    ! [X0] :
      ( r2_hidden(sK4(k6_relat_1(X0),X0),X0)
      | k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    inference(factoring,[],[f151])).

fof(f151,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK4(k6_relat_1(X6),X7),X7)
      | r2_hidden(sK4(k6_relat_1(X6),X7),X6)
      | k1_relat_1(k6_relat_1(X6)) = X7 ) ),
    inference(subsumption_resolution,[],[f148,f48])).

fof(f148,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK4(k6_relat_1(X6),X7),X7)
      | k1_relat_1(k6_relat_1(X6)) = X7
      | r2_hidden(sK4(k6_relat_1(X6),X7),X6)
      | ~ v1_relat_1(k6_relat_1(X6)) ) ),
    inference(resolution,[],[f37,f58])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK6(X0,X1)),X0)
      | r2_hidden(sK4(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f582,plain,(
    spl9_9 ),
    inference(avatar_contradiction_clause,[],[f581])).

fof(f581,plain,
    ( $false
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f447,f53])).

fof(f447,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl9_9 ),
    inference(backward_demodulation,[],[f359,f95])).

fof(f95,plain,
    ( ~ r1_tarski(k1_relat_1(k6_relat_1(sK0)),sK0)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl9_9
  <=> ~ r1_tarski(k1_relat_1(k6_relat_1(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f102,plain,
    ( ~ spl9_9
    | ~ spl9_11
    | spl9_3 ),
    inference(avatar_split_clause,[],[f74,f69,f100,f94])).

fof(f69,plain,
    ( spl9_3
  <=> k1_relat_1(k6_relat_1(sK0)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f74,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(k6_relat_1(sK0)))
    | ~ r1_tarski(k1_relat_1(k6_relat_1(sK0)),sK0)
    | ~ spl9_3 ),
    inference(extensionality_resolution,[],[f41,f70])).

fof(f70,plain,
    ( k1_relat_1(k6_relat_1(sK0)) != sK0
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f89,plain,
    ( ~ spl9_5
    | ~ spl9_7
    | spl9_1 ),
    inference(avatar_split_clause,[],[f72,f63,f87,f81])).

fof(f63,plain,
    ( spl9_1
  <=> k2_relat_1(k6_relat_1(sK0)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f72,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(k6_relat_1(sK0)))
    | ~ r1_tarski(k2_relat_1(k6_relat_1(sK0)),sK0)
    | ~ spl9_1 ),
    inference(extensionality_resolution,[],[f41,f64])).

fof(f64,plain,
    ( k2_relat_1(k6_relat_1(sK0)) != sK0
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f71,plain,
    ( ~ spl9_1
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f29,f69,f63])).

fof(f29,plain,
    ( k1_relat_1(k6_relat_1(sK0)) != sK0
    | k2_relat_1(k6_relat_1(sK0)) != sK0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( k2_relat_1(k6_relat_1(X0)) != X0
      | k1_relat_1(k6_relat_1(X0)) != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( k2_relat_1(k6_relat_1(X0)) = X0
        & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t71_relat_1.p',t71_relat_1)).
%------------------------------------------------------------------------------
