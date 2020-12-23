%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0021+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:03 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   44 (  68 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :  126 ( 273 expanded)
%              Number of equality atoms :   16 (  43 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f404,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f368,f383,f403])).

fof(f403,plain,(
    spl17_3 ),
    inference(avatar_contradiction_clause,[],[f402])).

fof(f402,plain,
    ( $false
    | spl17_3 ),
    inference(subsumption_resolution,[],[f397,f235])).

fof(f235,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f113])).

fof(f113,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f397,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl17_3 ),
    inference(resolution,[],[f374,f197])).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f374,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK0,sK2))
    | spl17_3 ),
    inference(subsumption_resolution,[],[f370,f163])).

fof(f163,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f370,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK0,sK2))
    | ~ r1_tarski(sK0,k2_xboole_0(sK0,sK2))
    | spl17_3 ),
    inference(resolution,[],[f363,f147])).

fof(f147,plain,(
    ! [X3] :
      ( r1_tarski(sK1,X3)
      | ~ r1_tarski(sK2,X3)
      | ~ r1_tarski(sK0,X3) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,
    ( sK1 != k2_xboole_0(sK0,sK2)
    & ! [X3] :
        ( r1_tarski(sK1,X3)
        | ~ r1_tarski(sK2,X3)
        | ~ r1_tarski(sK0,X3) )
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f66,f98])).

fof(f98,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(X0,X2) != X1
        & ! [X3] :
            ( r1_tarski(X1,X3)
            | ~ r1_tarski(X2,X3)
            | ~ r1_tarski(X0,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
   => ( sK1 != k2_xboole_0(sK0,sK2)
      & ! [X3] :
          ( r1_tarski(sK1,X3)
          | ~ r1_tarski(sK2,X3)
          | ~ r1_tarski(sK0,X3) )
      & r1_tarski(sK2,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) != X1
      & ! [X3] :
          ( r1_tarski(X1,X3)
          | ~ r1_tarski(X2,X3)
          | ~ r1_tarski(X0,X3) )
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) != X1
      & ! [X3] :
          ( r1_tarski(X1,X3)
          | ~ r1_tarski(X2,X3)
          | ~ r1_tarski(X0,X3) )
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( ! [X3] :
              ( ( r1_tarski(X2,X3)
                & r1_tarski(X0,X3) )
             => r1_tarski(X1,X3) )
          & r1_tarski(X2,X1)
          & r1_tarski(X0,X1) )
       => k2_xboole_0(X0,X2) = X1 ) ),
    inference(negated_conjecture,[],[f44])).

fof(f44,conjecture,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f363,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK0,sK2))
    | spl17_3 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl17_3
  <=> r1_tarski(sK1,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_3])])).

fof(f383,plain,(
    spl17_4 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | spl17_4 ),
    inference(subsumption_resolution,[],[f381,f145])).

fof(f145,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f99])).

fof(f381,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl17_4 ),
    inference(subsumption_resolution,[],[f379,f146])).

fof(f146,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f99])).

fof(f379,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ r1_tarski(sK0,sK1)
    | spl17_4 ),
    inference(resolution,[],[f367,f201])).

fof(f201,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f91])).

fof(f91,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f57])).

fof(f57,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f367,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK2),sK1)
    | spl17_4 ),
    inference(avatar_component_clause,[],[f365])).

fof(f365,plain,
    ( spl17_4
  <=> r1_tarski(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_4])])).

fof(f368,plain,
    ( ~ spl17_3
    | ~ spl17_4 ),
    inference(avatar_split_clause,[],[f327,f365,f361])).

fof(f327,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK2),sK1)
    | ~ r1_tarski(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f264,f249])).

fof(f249,plain,(
    ~ sQ16_eqProxy(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(equality_proxy_replacement,[],[f148,f246])).

fof(f246,plain,(
    ! [X1,X0] :
      ( sQ16_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ16_eqProxy])])).

fof(f148,plain,(
    sK1 != k2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f99])).

fof(f264,plain,(
    ! [X0,X1] :
      ( sQ16_eqProxy(X0,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f184,f246])).

fof(f184,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f114])).
%------------------------------------------------------------------------------
