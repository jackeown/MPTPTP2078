%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t10_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:24 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   21 (  22 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  38 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f65,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f64])).

fof(f64,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f63])).

fof(f63,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f57,f46])).

fof(f46,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t10_ordinal1.p',d1_tarski)).

fof(f57,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl3_1 ),
    inference(resolution,[],[f41,f52])).

fof(f52,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_1
  <=> ~ r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t10_ordinal1.p',d3_xboole_0)).

fof(f53,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f40,f51])).

fof(f40,plain,(
    ~ r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0))) ),
    inference(definition_unfolding,[],[f25,f27])).

fof(f27,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t10_ordinal1.p',d1_ordinal1)).

fof(f25,plain,(
    ~ r2_hidden(sK0,k1_ordinal1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] : ~ r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t10_ordinal1.p',t10_ordinal1)).
%------------------------------------------------------------------------------
