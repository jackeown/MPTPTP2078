%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0019+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 (  59 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :   93 ( 148 expanded)
%              Number of equality atoms :   15 (  34 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f423,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f394,f409,f421])).

fof(f421,plain,(
    spl16_6 ),
    inference(avatar_contradiction_clause,[],[f420])).

fof(f420,plain,
    ( $false
    | spl16_6 ),
    inference(subsumption_resolution,[],[f419,f138])).

fof(f138,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,
    ( sK1 != k2_xboole_0(sK0,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f62,f89])).

fof(f89,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(X0,X1) != X1
        & r1_tarski(X0,X1) )
   => ( sK1 != k2_xboole_0(sK0,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(X0,X1) != X1
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => k2_xboole_0(X0,X1) = X1 ) ),
    inference(negated_conjecture,[],[f42])).

fof(f42,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f419,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl16_6 ),
    inference(subsumption_resolution,[],[f413,f227])).

fof(f227,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f413,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ r1_tarski(sK0,sK1)
    | spl16_6 ),
    inference(resolution,[],[f328,f193])).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f55])).

fof(f55,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f328,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),sK1)
    | spl16_6 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl16_6
  <=> r1_tarski(k2_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_6])])).

fof(f409,plain,
    ( ~ spl16_6
    | ~ spl16_5 ),
    inference(avatar_split_clause,[],[f408,f322,f326])).

fof(f322,plain,
    ( spl16_5
  <=> r1_tarski(sK1,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_5])])).

fof(f408,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),sK1)
    | ~ spl16_5 ),
    inference(subsumption_resolution,[],[f404,f317])).

fof(f317,plain,(
    ~ sQ15_eqProxy(k2_xboole_0(sK0,sK1),sK1) ),
    inference(resolution,[],[f241,f276])).

fof(f276,plain,(
    ! [X0,X1] :
      ( ~ sQ15_eqProxy(X0,X1)
      | sQ15_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f238])).

fof(f238,plain,(
    ! [X1,X0] :
      ( sQ15_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ15_eqProxy])])).

fof(f241,plain,(
    ~ sQ15_eqProxy(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(equality_proxy_replacement,[],[f139,f238])).

fof(f139,plain,(
    sK1 != k2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f90])).

fof(f404,plain,
    ( sQ15_eqProxy(k2_xboole_0(sK0,sK1),sK1)
    | ~ r1_tarski(k2_xboole_0(sK0,sK1),sK1)
    | ~ spl16_5 ),
    inference(resolution,[],[f323,f255])).

fof(f255,plain,(
    ! [X0,X1] :
      ( sQ15_eqProxy(X0,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f174,f238])).

fof(f174,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f323,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK0,sK1))
    | ~ spl16_5 ),
    inference(avatar_component_clause,[],[f322])).

fof(f394,plain,(
    spl16_5 ),
    inference(avatar_contradiction_clause,[],[f393])).

fof(f393,plain,
    ( $false
    | spl16_5 ),
    inference(subsumption_resolution,[],[f387,f227])).

fof(f387,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl16_5 ),
    inference(resolution,[],[f324,f189])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f324,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK0,sK1))
    | spl16_5 ),
    inference(avatar_component_clause,[],[f322])).
%------------------------------------------------------------------------------
