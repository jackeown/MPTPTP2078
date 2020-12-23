%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:22 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 181 expanded)
%              Number of leaves         :   34 (  84 expanded)
%              Depth                    :    7
%              Number of atoms          :  269 ( 395 expanded)
%              Number of equality atoms :   67 ( 120 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f309,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f66,f70,f78,f91,f95,f105,f138,f152,f177,f182,f187,f192,f210,f222,f261,f290])).

fof(f290,plain,
    ( ~ spl5_7
    | ~ spl5_17
    | spl5_23
    | ~ spl5_28
    | ~ spl5_33 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | ~ spl5_7
    | ~ spl5_17
    | spl5_23
    | ~ spl5_28
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f186,f288])).

fof(f288,plain,
    ( ! [X6] : k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,X6))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X6))
    | ~ spl5_7
    | ~ spl5_17
    | ~ spl5_28
    | ~ spl5_33 ),
    inference(forward_demodulation,[],[f287,f77])).

fof(f77,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl5_7
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f287,plain,
    ( ! [X6] : k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,X6))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,X6)))
    | ~ spl5_17
    | ~ spl5_28
    | ~ spl5_33 ),
    inference(forward_demodulation,[],[f265,f151])).

fof(f151,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl5_17
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f265,plain,
    ( ! [X6] : k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,X6))) = k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,X6)))
    | ~ spl5_28
    | ~ spl5_33 ),
    inference(superposition,[],[f260,f221])).

fof(f221,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl5_28
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f260,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl5_33
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f186,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | spl5_23 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl5_23
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f261,plain,(
    spl5_33 ),
    inference(avatar_split_clause,[],[f45,f259])).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f40,f33,f33,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f222,plain,
    ( spl5_28
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f216,f207,f136,f103,f52,f219])).

fof(f52,plain,
    ( spl5_2
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f103,plain,
    ( spl5_12
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f136,plain,
    ( spl5_16
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f207,plain,
    ( spl5_27
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f216,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f215,f104])).

fof(f104,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f103])).

fof(f215,plain,
    ( k4_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f211,f53])).

fof(f53,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f211,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl5_16
    | ~ spl5_27 ),
    inference(superposition,[],[f137,f209])).

fof(f209,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f207])).

fof(f137,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f136])).

fof(f210,plain,
    ( spl5_27
    | ~ spl5_4
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f193,f190,f60,f207])).

fof(f60,plain,
    ( spl5_4
  <=> ! [X0] :
        ( r2_xboole_0(k1_xboole_0,X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f190,plain,
    ( spl5_24
  <=> ! [X0] : ~ r2_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f193,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_4
    | ~ spl5_24 ),
    inference(resolution,[],[f191,f61])).

fof(f61,plain,
    ( ! [X0] :
        ( r2_xboole_0(k1_xboole_0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f191,plain,
    ( ! [X0] : ~ r2_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f190])).

fof(f192,plain,
    ( spl5_24
    | ~ spl5_10
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f188,f180,f93,f190])).

fof(f93,plain,
    ( spl5_10
  <=> ! [X1,X0] :
        ( r2_hidden(sK4(X0,X1),X1)
        | ~ r2_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f180,plain,
    ( spl5_22
  <=> ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f188,plain,
    ( ! [X0] : ~ r2_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl5_10
    | ~ spl5_22 ),
    inference(resolution,[],[f181,f94])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1),X1)
        | ~ r2_xboole_0(X0,X1) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f93])).

fof(f181,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f180])).

fof(f187,plain,(
    ~ spl5_23 ),
    inference(avatar_split_clause,[],[f41,f184])).

fof(f41,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(definition_unfolding,[],[f27,f33,f33])).

fof(f27,plain,(
    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1) )
   => ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2)
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f182,plain,
    ( spl5_22
    | ~ spl5_1
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f178,f175,f47,f180])).

fof(f47,plain,
    ( spl5_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f175,plain,
    ( spl5_21
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f178,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl5_1
    | ~ spl5_21 ),
    inference(resolution,[],[f176,f49])).

fof(f49,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f176,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f175])).

fof(f177,plain,(
    spl5_21 ),
    inference(avatar_split_clause,[],[f43,f175])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f36,f33])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f152,plain,
    ( spl5_17
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f146,f136,f103,f68,f52,f150])).

fof(f68,plain,
    ( spl5_6
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f146,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(backward_demodulation,[],[f69,f145])).

fof(f145,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f144,f104])).

fof(f144,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),X0)
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f139,f53])).

fof(f139,plain,
    ( ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),X0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0)
    | ~ spl5_6
    | ~ spl5_16 ),
    inference(superposition,[],[f137,f69])).

fof(f69,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f138,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f34,f136])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f105,plain,
    ( spl5_12
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f100,f89,f56,f103])).

fof(f56,plain,
    ( spl5_3
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f89,plain,
    ( spl5_9
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f100,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(resolution,[],[f90,f57])).

fof(f57,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f89])).

fof(f95,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f38,f93])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f91,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f37,f89])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f78,plain,
    ( spl5_7
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f71,f64,f52,f76])).

fof(f64,plain,
    ( spl5_5
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f71,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(superposition,[],[f65,f53])).

fof(f65,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f70,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f42,f68])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f28,f33])).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f66,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f32,f64])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f62,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f30,f60])).

fof(f30,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).

fof(f58,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f31,f56])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f54,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f29,f52])).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f50,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f26,f47])).

fof(f26,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:21:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.41  % (14891)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.42  % (14891)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f309,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f66,f70,f78,f91,f95,f105,f138,f152,f177,f182,f187,f192,f210,f222,f261,f290])).
% 0.19/0.42  fof(f290,plain,(
% 0.19/0.42    ~spl5_7 | ~spl5_17 | spl5_23 | ~spl5_28 | ~spl5_33),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f289])).
% 0.19/0.42  fof(f289,plain,(
% 0.19/0.42    $false | (~spl5_7 | ~spl5_17 | spl5_23 | ~spl5_28 | ~spl5_33)),
% 0.19/0.42    inference(subsumption_resolution,[],[f186,f288])).
% 0.19/0.42  fof(f288,plain,(
% 0.19/0.42    ( ! [X6] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,X6))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X6))) ) | (~spl5_7 | ~spl5_17 | ~spl5_28 | ~spl5_33)),
% 0.19/0.42    inference(forward_demodulation,[],[f287,f77])).
% 0.19/0.42  fof(f77,plain,(
% 0.19/0.42    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl5_7),
% 0.19/0.42    inference(avatar_component_clause,[],[f76])).
% 0.19/0.42  fof(f76,plain,(
% 0.19/0.42    spl5_7 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.19/0.42  fof(f287,plain,(
% 0.19/0.42    ( ! [X6] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,X6))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,X6)))) ) | (~spl5_17 | ~spl5_28 | ~spl5_33)),
% 0.19/0.42    inference(forward_demodulation,[],[f265,f151])).
% 0.19/0.42  fof(f151,plain,(
% 0.19/0.42    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl5_17),
% 0.19/0.42    inference(avatar_component_clause,[],[f150])).
% 0.19/0.42  fof(f150,plain,(
% 0.19/0.42    spl5_17 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.19/0.42  fof(f265,plain,(
% 0.19/0.42    ( ! [X6] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,X6))) = k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,X6)))) ) | (~spl5_28 | ~spl5_33)),
% 0.19/0.42    inference(superposition,[],[f260,f221])).
% 0.19/0.42  fof(f221,plain,(
% 0.19/0.42    sK0 = k4_xboole_0(sK0,sK1) | ~spl5_28),
% 0.19/0.42    inference(avatar_component_clause,[],[f219])).
% 0.19/0.42  fof(f219,plain,(
% 0.19/0.42    spl5_28 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.19/0.42  fof(f260,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ) | ~spl5_33),
% 0.19/0.42    inference(avatar_component_clause,[],[f259])).
% 0.19/0.42  fof(f259,plain,(
% 0.19/0.42    spl5_33 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.19/0.42  fof(f186,plain,(
% 0.19/0.42    k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | spl5_23),
% 0.19/0.42    inference(avatar_component_clause,[],[f184])).
% 0.19/0.42  fof(f184,plain,(
% 0.19/0.42    spl5_23 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.19/0.42  fof(f261,plain,(
% 0.19/0.42    spl5_33),
% 0.19/0.42    inference(avatar_split_clause,[],[f45,f259])).
% 0.19/0.42  fof(f45,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.19/0.42    inference(definition_unfolding,[],[f40,f33,f33,f33])).
% 0.19/0.42  fof(f33,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f10])).
% 0.19/0.42  fof(f10,axiom,(
% 0.19/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.42  fof(f40,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f6])).
% 0.19/0.42  fof(f6,axiom,(
% 0.19/0.42    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.19/0.42  fof(f222,plain,(
% 0.19/0.42    spl5_28 | ~spl5_2 | ~spl5_12 | ~spl5_16 | ~spl5_27),
% 0.19/0.42    inference(avatar_split_clause,[],[f216,f207,f136,f103,f52,f219])).
% 0.19/0.42  fof(f52,plain,(
% 0.19/0.42    spl5_2 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.42  fof(f103,plain,(
% 0.19/0.42    spl5_12 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.19/0.42  fof(f136,plain,(
% 0.19/0.42    spl5_16 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.19/0.42  fof(f207,plain,(
% 0.19/0.42    spl5_27 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.19/0.42  fof(f216,plain,(
% 0.19/0.42    sK0 = k4_xboole_0(sK0,sK1) | (~spl5_2 | ~spl5_12 | ~spl5_16 | ~spl5_27)),
% 0.19/0.42    inference(forward_demodulation,[],[f215,f104])).
% 0.19/0.42  fof(f104,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) ) | ~spl5_12),
% 0.19/0.42    inference(avatar_component_clause,[],[f103])).
% 0.19/0.42  fof(f215,plain,(
% 0.19/0.42    k4_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) | (~spl5_2 | ~spl5_16 | ~spl5_27)),
% 0.19/0.42    inference(forward_demodulation,[],[f211,f53])).
% 0.19/0.42  fof(f53,plain,(
% 0.19/0.42    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl5_2),
% 0.19/0.42    inference(avatar_component_clause,[],[f52])).
% 0.19/0.42  fof(f211,plain,(
% 0.19/0.42    k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | (~spl5_16 | ~spl5_27)),
% 0.19/0.42    inference(superposition,[],[f137,f209])).
% 0.19/0.42  fof(f209,plain,(
% 0.19/0.42    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_27),
% 0.19/0.42    inference(avatar_component_clause,[],[f207])).
% 0.19/0.42  fof(f137,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl5_16),
% 0.19/0.42    inference(avatar_component_clause,[],[f136])).
% 0.19/0.42  fof(f210,plain,(
% 0.19/0.42    spl5_27 | ~spl5_4 | ~spl5_24),
% 0.19/0.42    inference(avatar_split_clause,[],[f193,f190,f60,f207])).
% 0.19/0.42  fof(f60,plain,(
% 0.19/0.42    spl5_4 <=> ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.19/0.42  fof(f190,plain,(
% 0.19/0.42    spl5_24 <=> ! [X0] : ~r2_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.19/0.42  fof(f193,plain,(
% 0.19/0.42    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl5_4 | ~spl5_24)),
% 0.19/0.42    inference(resolution,[],[f191,f61])).
% 0.19/0.42  fof(f61,plain,(
% 0.19/0.42    ( ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0) ) | ~spl5_4),
% 0.19/0.42    inference(avatar_component_clause,[],[f60])).
% 0.19/0.42  fof(f191,plain,(
% 0.19/0.42    ( ! [X0] : (~r2_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | ~spl5_24),
% 0.19/0.42    inference(avatar_component_clause,[],[f190])).
% 0.19/0.42  fof(f192,plain,(
% 0.19/0.42    spl5_24 | ~spl5_10 | ~spl5_22),
% 0.19/0.42    inference(avatar_split_clause,[],[f188,f180,f93,f190])).
% 0.19/0.42  fof(f93,plain,(
% 0.19/0.42    spl5_10 <=> ! [X1,X0] : (r2_hidden(sK4(X0,X1),X1) | ~r2_xboole_0(X0,X1))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.19/0.42  fof(f180,plain,(
% 0.19/0.42    spl5_22 <=> ! [X0] : ~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.19/0.42  fof(f188,plain,(
% 0.19/0.42    ( ! [X0] : (~r2_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | (~spl5_10 | ~spl5_22)),
% 0.19/0.42    inference(resolution,[],[f181,f94])).
% 0.19/0.42  fof(f94,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | ~r2_xboole_0(X0,X1)) ) | ~spl5_10),
% 0.19/0.42    inference(avatar_component_clause,[],[f93])).
% 0.19/0.42  fof(f181,plain,(
% 0.19/0.42    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | ~spl5_22),
% 0.19/0.42    inference(avatar_component_clause,[],[f180])).
% 0.19/0.42  fof(f187,plain,(
% 0.19/0.42    ~spl5_23),
% 0.19/0.42    inference(avatar_split_clause,[],[f41,f184])).
% 0.19/0.42  fof(f41,plain,(
% 0.19/0.42    k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.19/0.42    inference(definition_unfolding,[],[f27,f33,f33])).
% 0.19/0.42  fof(f27,plain,(
% 0.19/0.42    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)),
% 0.19/0.42    inference(cnf_transformation,[],[f21])).
% 0.19/0.42  fof(f21,plain,(
% 0.19/0.42    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1)),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f20])).
% 0.19/0.42  fof(f20,plain,(
% 0.19/0.42    ? [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2) & r1_xboole_0(X0,X1)) => (k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f15,plain,(
% 0.19/0.42    ? [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2) & r1_xboole_0(X0,X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f13])).
% 0.19/0.42  fof(f13,negated_conjecture,(
% 0.19/0.42    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.19/0.42    inference(negated_conjecture,[],[f12])).
% 0.19/0.42  fof(f12,conjecture,(
% 0.19/0.42    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.19/0.42  fof(f182,plain,(
% 0.19/0.42    spl5_22 | ~spl5_1 | ~spl5_21),
% 0.19/0.42    inference(avatar_split_clause,[],[f178,f175,f47,f180])).
% 0.19/0.42  fof(f47,plain,(
% 0.19/0.42    spl5_1 <=> r1_xboole_0(sK0,sK1)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.42  fof(f175,plain,(
% 0.19/0.42    spl5_21 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.19/0.42  fof(f178,plain,(
% 0.19/0.42    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | (~spl5_1 | ~spl5_21)),
% 0.19/0.42    inference(resolution,[],[f176,f49])).
% 0.19/0.42  fof(f49,plain,(
% 0.19/0.42    r1_xboole_0(sK0,sK1) | ~spl5_1),
% 0.19/0.42    inference(avatar_component_clause,[],[f47])).
% 0.19/0.42  fof(f176,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl5_21),
% 0.19/0.42    inference(avatar_component_clause,[],[f175])).
% 0.19/0.42  fof(f177,plain,(
% 0.19/0.42    spl5_21),
% 0.19/0.42    inference(avatar_split_clause,[],[f43,f175])).
% 0.19/0.42  fof(f43,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.19/0.42    inference(definition_unfolding,[],[f36,f33])).
% 0.19/0.42  fof(f36,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f23])).
% 0.19/0.42  fof(f23,plain,(
% 0.19/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f22])).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f17,plain,(
% 0.19/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.19/0.42    inference(ennf_transformation,[],[f14])).
% 0.19/0.42  fof(f14,plain,(
% 0.19/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.42    inference(rectify,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.19/0.42  fof(f152,plain,(
% 0.19/0.42    spl5_17 | ~spl5_2 | ~spl5_6 | ~spl5_12 | ~spl5_16),
% 0.19/0.42    inference(avatar_split_clause,[],[f146,f136,f103,f68,f52,f150])).
% 0.19/0.42  fof(f68,plain,(
% 0.19/0.42    spl5_6 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.19/0.42  fof(f146,plain,(
% 0.19/0.42    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl5_2 | ~spl5_6 | ~spl5_12 | ~spl5_16)),
% 0.19/0.42    inference(backward_demodulation,[],[f69,f145])).
% 0.19/0.42  fof(f145,plain,(
% 0.19/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl5_2 | ~spl5_6 | ~spl5_12 | ~spl5_16)),
% 0.19/0.42    inference(forward_demodulation,[],[f144,f104])).
% 0.19/0.42  fof(f144,plain,(
% 0.19/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),X0)) ) | (~spl5_2 | ~spl5_6 | ~spl5_16)),
% 0.19/0.42    inference(forward_demodulation,[],[f139,f53])).
% 0.19/0.42  fof(f139,plain,(
% 0.19/0.42    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),X0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0)) ) | (~spl5_6 | ~spl5_16)),
% 0.19/0.42    inference(superposition,[],[f137,f69])).
% 0.19/0.42  fof(f69,plain,(
% 0.19/0.42    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ) | ~spl5_6),
% 0.19/0.42    inference(avatar_component_clause,[],[f68])).
% 0.19/0.42  fof(f138,plain,(
% 0.19/0.42    spl5_16),
% 0.19/0.42    inference(avatar_split_clause,[],[f34,f136])).
% 0.19/0.42  fof(f34,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f9])).
% 0.19/0.42  fof(f9,axiom,(
% 0.19/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.19/0.42  fof(f105,plain,(
% 0.19/0.42    spl5_12 | ~spl5_3 | ~spl5_9),
% 0.19/0.42    inference(avatar_split_clause,[],[f100,f89,f56,f103])).
% 0.19/0.42  fof(f56,plain,(
% 0.19/0.42    spl5_3 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.42  fof(f89,plain,(
% 0.19/0.42    spl5_9 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.19/0.42  fof(f100,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) ) | (~spl5_3 | ~spl5_9)),
% 0.19/0.42    inference(resolution,[],[f90,f57])).
% 0.19/0.42  fof(f57,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl5_3),
% 0.19/0.42    inference(avatar_component_clause,[],[f56])).
% 0.19/0.42  fof(f90,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl5_9),
% 0.19/0.42    inference(avatar_component_clause,[],[f89])).
% 0.19/0.42  fof(f95,plain,(
% 0.19/0.42    spl5_10),
% 0.19/0.42    inference(avatar_split_clause,[],[f38,f93])).
% 0.19/0.42  fof(f38,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f25])).
% 0.19/0.42  fof(f25,plain,(
% 0.19/0.42    ! [X0,X1] : ((~r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f24])).
% 0.19/0.42  fof(f24,plain,(
% 0.19/0.42    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),X1)))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f19,plain,(
% 0.19/0.42    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f3])).
% 0.19/0.42  fof(f3,axiom,(
% 0.19/0.42    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).
% 0.19/0.42  fof(f91,plain,(
% 0.19/0.42    spl5_9),
% 0.19/0.42    inference(avatar_split_clause,[],[f37,f89])).
% 0.19/0.42  fof(f37,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f18])).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.19/0.42  fof(f78,plain,(
% 0.19/0.42    spl5_7 | ~spl5_2 | ~spl5_5),
% 0.19/0.42    inference(avatar_split_clause,[],[f71,f64,f52,f76])).
% 0.19/0.42  fof(f64,plain,(
% 0.19/0.42    spl5_5 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.19/0.42  fof(f71,plain,(
% 0.19/0.42    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl5_2 | ~spl5_5)),
% 0.19/0.42    inference(superposition,[],[f65,f53])).
% 0.19/0.42  fof(f65,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl5_5),
% 0.19/0.42    inference(avatar_component_clause,[],[f64])).
% 0.19/0.42  fof(f70,plain,(
% 0.19/0.42    spl5_6),
% 0.19/0.42    inference(avatar_split_clause,[],[f42,f68])).
% 0.19/0.42  fof(f42,plain,(
% 0.19/0.42    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.19/0.42    inference(definition_unfolding,[],[f28,f33])).
% 0.19/0.42  fof(f28,plain,(
% 0.19/0.42    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f7])).
% 0.19/0.42  fof(f7,axiom,(
% 0.19/0.42    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.19/0.42  fof(f66,plain,(
% 0.19/0.42    spl5_5),
% 0.19/0.42    inference(avatar_split_clause,[],[f32,f64])).
% 0.19/0.42  fof(f32,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.19/0.42  fof(f62,plain,(
% 0.19/0.42    spl5_4),
% 0.19/0.42    inference(avatar_split_clause,[],[f30,f60])).
% 0.19/0.42  fof(f30,plain,(
% 0.19/0.42    ( ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f16])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0)),
% 0.19/0.42    inference(ennf_transformation,[],[f11])).
% 0.19/0.42  fof(f11,axiom,(
% 0.19/0.42    ! [X0] : (k1_xboole_0 != X0 => r2_xboole_0(k1_xboole_0,X0))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).
% 0.19/0.42  fof(f58,plain,(
% 0.19/0.42    spl5_3),
% 0.19/0.42    inference(avatar_split_clause,[],[f31,f56])).
% 0.19/0.42  fof(f31,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f8])).
% 0.19/0.42  fof(f8,axiom,(
% 0.19/0.42    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.19/0.42  fof(f54,plain,(
% 0.19/0.42    spl5_2),
% 0.19/0.42    inference(avatar_split_clause,[],[f29,f52])).
% 0.19/0.42  fof(f29,plain,(
% 0.19/0.42    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f5])).
% 0.19/0.42  fof(f5,axiom,(
% 0.19/0.42    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.19/0.42  fof(f50,plain,(
% 0.19/0.42    spl5_1),
% 0.19/0.42    inference(avatar_split_clause,[],[f26,f47])).
% 0.19/0.42  fof(f26,plain,(
% 0.19/0.42    r1_xboole_0(sK0,sK1)),
% 0.19/0.42    inference(cnf_transformation,[],[f21])).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (14891)------------------------------
% 0.19/0.42  % (14891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (14891)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (14891)Memory used [KB]: 6268
% 0.19/0.42  % (14891)Time elapsed: 0.031 s
% 0.19/0.42  % (14891)------------------------------
% 0.19/0.42  % (14891)------------------------------
% 0.19/0.42  % (14883)Success in time 0.075 s
%------------------------------------------------------------------------------
