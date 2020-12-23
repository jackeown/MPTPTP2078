%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t62_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:30 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   27 (  34 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   50 (  64 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f50,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f38,f42,f48,f49])).

fof(f49,plain,
    ( k1_xboole_0 != sK0
    | r2_xboole_0(k1_xboole_0,sK0)
    | ~ r2_xboole_0(sK0,k1_xboole_0) ),
    introduced(theory_axiom,[])).

fof(f48,plain,
    ( spl1_6
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f43,f40,f46])).

fof(f46,plain,
    ( spl1_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f40,plain,
    ( spl1_4
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f43,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_4 ),
    inference(resolution,[],[f41,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t62_xboole_1.p',t3_xboole_1)).

fof(f41,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f42,plain,
    ( spl1_4
    | ~ spl1_0 ),
    inference(avatar_split_clause,[],[f34,f30,f40])).

fof(f30,plain,
    ( spl1_0
  <=> r2_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_0])])).

fof(f34,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl1_0 ),
    inference(resolution,[],[f31,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t62_xboole_1.p',d8_xboole_0)).

fof(f31,plain,
    ( r2_xboole_0(sK0,k1_xboole_0)
    | ~ spl1_0 ),
    inference(avatar_component_clause,[],[f30])).

fof(f38,plain,
    ( ~ spl1_3
    | ~ spl1_0 ),
    inference(avatar_split_clause,[],[f33,f30,f36])).

fof(f36,plain,
    ( spl1_3
  <=> ~ r2_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f33,plain,
    ( ~ r2_xboole_0(k1_xboole_0,sK0)
    | ~ spl1_0 ),
    inference(resolution,[],[f31,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t62_xboole_1.p',antisymmetry_r2_xboole_0)).

fof(f32,plain,(
    spl1_0 ),
    inference(avatar_split_clause,[],[f21,f30])).

fof(f21,plain,(
    r2_xboole_0(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] : r2_xboole_0(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t62_xboole_1.p',t62_xboole_1)).
%------------------------------------------------------------------------------
