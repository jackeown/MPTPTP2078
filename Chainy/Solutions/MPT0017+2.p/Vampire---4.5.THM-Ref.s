%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0017+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  37 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :   51 (  73 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f225,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f122,f129,f212])).

fof(f212,plain,
    ( ~ spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f200,f126,f119])).

fof(f119,plain,
    ( spl5_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f126,plain,
    ( spl5_3
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f200,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f96,f128,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f128,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f126])).

fof(f96,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f129,plain,
    ( ~ spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f124,f114,f126])).

fof(f114,plain,
    ( spl5_1
  <=> r1_tarski(sK0,k2_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f124,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | spl5_1 ),
    inference(forward_demodulation,[],[f116,f95])).

fof(f95,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f116,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK2,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f122,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f80,f119])).

fof(f80,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK2,sK1))
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f57,f67])).

fof(f67,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k2_xboole_0(X2,X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(sK0,k2_xboole_0(sK2,sK1))
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k2_xboole_0(X2,X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f40])).

fof(f40,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f117,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f81,f114])).

fof(f81,plain,(
    ~ r1_tarski(sK0,k2_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f68])).
%------------------------------------------------------------------------------
