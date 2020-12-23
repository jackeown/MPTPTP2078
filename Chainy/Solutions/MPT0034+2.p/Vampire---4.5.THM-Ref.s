%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0034+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  66 expanded)
%              Number of leaves         :   11 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   93 ( 161 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f328,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f139,f143,f147,f297,f300,f327])).

fof(f327,plain,
    ( ~ spl6_2
    | spl6_14 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | ~ spl6_2
    | spl6_14 ),
    inference(unit_resulting_resolution,[],[f142,f157,f296,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f296,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK3)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl6_14
  <=> r1_tarski(k3_xboole_0(sK0,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f157,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X3,X2),X2) ),
    inference(superposition,[],[f118,f117])).

fof(f117,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f118,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f142,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl6_2
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f300,plain,
    ( ~ spl6_3
    | spl6_13 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | ~ spl6_3
    | spl6_13 ),
    inference(unit_resulting_resolution,[],[f146,f118,f293,f125])).

fof(f293,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl6_13
  <=> r1_tarski(k3_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f146,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl6_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f297,plain,
    ( ~ spl6_13
    | ~ spl6_14
    | spl6_1 ),
    inference(avatar_split_clause,[],[f280,f137,f295,f292])).

fof(f137,plain,
    ( spl6_1
  <=> r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f280,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK3)
    | ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    | spl6_1 ),
    inference(resolution,[],[f108,f138])).

fof(f138,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f137])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f147,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f102,f145])).

fof(f102,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f75,f94])).

fof(f94,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f60])).

fof(f60,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    inference(negated_conjecture,[],[f59])).

fof(f59,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_xboole_1)).

fof(f143,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f103,f141])).

fof(f103,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f95])).

fof(f139,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f104,f137])).

fof(f104,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) ),
    inference(cnf_transformation,[],[f95])).
%------------------------------------------------------------------------------
