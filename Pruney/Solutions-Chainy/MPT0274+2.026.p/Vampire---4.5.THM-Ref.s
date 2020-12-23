%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:24 EST 2020

% Result     : Theorem 10.51s
% Output     : Refutation 10.51s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 402 expanded)
%              Number of leaves         :   38 ( 143 expanded)
%              Depth                    :   13
%              Number of atoms          :  480 (1147 expanded)
%              Number of equality atoms :  170 ( 504 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4168,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f140,f142,f1342,f1379,f1519,f1616,f1903,f2276,f2283,f2317,f2541,f2566,f2648,f2649,f4158,f4164,f4166,f4167])).

fof(f4167,plain,
    ( sK2 != k3_xboole_0(sK2,sK2)
    | r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,k3_xboole_0(sK2,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4166,plain,
    ( sK1 != sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | sK2 != k3_xboole_0(sK2,sK2)
    | r2_hidden(sK1,k3_xboole_0(sK2,sK2))
    | ~ r2_hidden(sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4164,plain,
    ( sK0 != sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4158,plain,
    ( spl7_129
    | spl7_130
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f4149,f365,f4155,f4151])).

fof(f4151,plain,
    ( spl7_129
  <=> sK0 = sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_129])])).

fof(f4155,plain,
    ( spl7_130
  <=> sK1 = sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_130])])).

fof(f365,plain,
    ( spl7_11
  <=> r2_hidden(sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f4149,plain,
    ( sK1 = sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | sK0 = sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl7_11 ),
    inference(duplicate_literal_removal,[],[f4135])).

fof(f4135,plain,
    ( sK1 = sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | sK0 = sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | sK0 = sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl7_11 ),
    inference(resolution,[],[f367,f124])).

fof(f124,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f87,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f76,f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f86,f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f95,f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f96,f97])).

fof(f97,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f95,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f86,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f87,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK6(X0,X1,X2,X3) != X2
              & sK6(X0,X1,X2,X3) != X1
              & sK6(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
          & ( sK6(X0,X1,X2,X3) = X2
            | sK6(X0,X1,X2,X3) = X1
            | sK6(X0,X1,X2,X3) = X0
            | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f53,f54])).

fof(f54,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK6(X0,X1,X2,X3) != X2
            & sK6(X0,X1,X2,X3) != X1
            & sK6(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
        & ( sK6(X0,X1,X2,X3) = X2
          | sK6(X0,X1,X2,X3) = X1
          | sK6(X0,X1,X2,X3) = X0
          | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f367,plain,
    ( r2_hidden(sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f365])).

fof(f2649,plain,
    ( spl7_11
    | spl7_4 ),
    inference(avatar_split_clause,[],[f2640,f164,f365])).

fof(f164,plain,
    ( spl7_4
  <=> r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f2640,plain,
    ( r2_hidden(sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | spl7_4 ),
    inference(resolution,[],[f166,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f166,plain,
    ( ~ r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f164])).

fof(f2648,plain,
    ( spl7_10
    | spl7_4 ),
    inference(avatar_split_clause,[],[f2639,f164,f360])).

fof(f360,plain,
    ( spl7_10
  <=> r2_hidden(sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f2639,plain,
    ( r2_hidden(sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2)
    | spl7_4 ),
    inference(resolution,[],[f166,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f2566,plain,
    ( ~ spl7_4
    | spl7_3 ),
    inference(avatar_split_clause,[],[f2565,f135,f164])).

fof(f135,plain,
    ( spl7_3
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f2565,plain,
    ( ~ r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | spl7_3 ),
    inference(trivial_inequality_removal,[],[f2564])).

fof(f2564,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | ~ r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | spl7_3 ),
    inference(forward_demodulation,[],[f2558,f60])).

fof(f60,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f2558,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k1_xboole_0)
    | ~ r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | spl7_3 ),
    inference(superposition,[],[f137,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f137,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f2541,plain,
    ( ~ spl7_1
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f2530])).

fof(f2530,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(resolution,[],[f1931,f165])).

fof(f165,plain,
    ( r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f164])).

fof(f1931,plain,
    ( ! [X14,X15] : ~ r1_xboole_0(sK2,k6_enumset1(X14,X14,X14,X14,X14,X14,sK0,X15))
    | ~ spl7_1 ),
    inference(resolution,[],[f1909,f121])).

fof(f121,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f89,f101])).

fof(f89,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1909,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | ~ r1_xboole_0(sK2,X0) )
    | ~ spl7_1 ),
    inference(resolution,[],[f129,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f129,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl7_1
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f2317,plain,
    ( spl7_95
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f2312,f896,f2314])).

fof(f2314,plain,
    ( spl7_95
  <=> sK2 = k3_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).

fof(f896,plain,
    ( spl7_36
  <=> r1_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f2312,plain,
    ( sK2 = k3_xboole_0(sK2,sK2)
    | ~ spl7_36 ),
    inference(resolution,[],[f897,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f897,plain,
    ( r1_tarski(sK2,sK2)
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f896])).

fof(f2283,plain,
    ( spl7_53
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f2279,f1277,f1351])).

fof(f1351,plain,
    ( spl7_53
  <=> k1_xboole_0 = k3_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f1277,plain,
    ( spl7_48
  <=> r1_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f2279,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k1_xboole_0)
    | ~ spl7_48 ),
    inference(resolution,[],[f1279,f74])).

fof(f1279,plain,
    ( r1_xboole_0(sK2,k1_xboole_0)
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f1277])).

fof(f2276,plain,(
    ~ spl7_76 ),
    inference(avatar_contradiction_clause,[],[f2260])).

fof(f2260,plain,
    ( $false
    | ~ spl7_76 ),
    inference(resolution,[],[f1684,f1615])).

fof(f1615,plain,
    ( r2_hidden(sK5(sK2,k1_xboole_0),k1_xboole_0)
    | ~ spl7_76 ),
    inference(avatar_component_clause,[],[f1613])).

fof(f1613,plain,
    ( spl7_76
  <=> r2_hidden(sK5(sK2,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).

fof(f1684,plain,
    ( ! [X2] : ~ r2_hidden(sK5(sK2,k1_xboole_0),X2)
    | ~ spl7_76 ),
    inference(duplicate_literal_removal,[],[f1683])).

fof(f1683,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK5(sK2,k1_xboole_0),X2)
        | ~ r2_hidden(sK5(sK2,k1_xboole_0),X2) )
    | ~ spl7_76 ),
    inference(forward_demodulation,[],[f1676,f60])).

fof(f1676,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK5(sK2,k1_xboole_0),X2)
        | ~ r2_hidden(sK5(sK2,k1_xboole_0),k5_xboole_0(X2,k1_xboole_0)) )
    | ~ spl7_76 ),
    inference(resolution,[],[f1615,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f1903,plain,
    ( ~ spl7_2
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f1892])).

fof(f1892,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(resolution,[],[f1074,f165])).

fof(f1074,plain,
    ( ! [X12,X13] : ~ r1_xboole_0(sK2,k6_enumset1(X12,X12,X12,X12,X12,X12,X13,sK1))
    | ~ spl7_2 ),
    inference(resolution,[],[f1037,f119])).

fof(f119,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f90,f101])).

fof(f90,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1037,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ r1_xboole_0(sK2,X0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f133,f72])).

fof(f133,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl7_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1616,plain,
    ( spl7_76
    | spl7_48 ),
    inference(avatar_split_clause,[],[f1603,f1277,f1613])).

fof(f1603,plain,
    ( r2_hidden(sK5(sK2,k1_xboole_0),k1_xboole_0)
    | spl7_48 ),
    inference(resolution,[],[f1278,f71])).

fof(f1278,plain,
    ( ~ r1_xboole_0(sK2,k1_xboole_0)
    | spl7_48 ),
    inference(avatar_component_clause,[],[f1277])).

fof(f1519,plain,
    ( spl7_36
    | ~ spl7_53 ),
    inference(avatar_split_clause,[],[f1518,f1351,f896])).

fof(f1518,plain,
    ( r1_tarski(sK2,sK2)
    | ~ spl7_53 ),
    inference(forward_demodulation,[],[f1495,f60])).

fof(f1495,plain,
    ( r1_tarski(k5_xboole_0(sK2,k1_xboole_0),k5_xboole_0(sK2,k1_xboole_0))
    | ~ spl7_53 ),
    inference(superposition,[],[f106,f1353])).

fof(f1353,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k1_xboole_0)
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f1351])).

fof(f106,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f64,f67])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

fof(f1379,plain,
    ( spl7_4
    | ~ spl7_52
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f1363,f135,f1339,f164])).

fof(f1339,plain,
    ( spl7_52
  <=> r2_hidden(sK4(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f1363,plain,
    ( ~ r2_hidden(sK4(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl7_3 ),
    inference(resolution,[],[f1061,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f1061,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
        | ~ r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) )
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f1056])).

fof(f1056,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | ~ r2_hidden(X2,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
        | ~ r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) )
    | ~ spl7_3 ),
    inference(superposition,[],[f82,f136])).

fof(f136,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f1342,plain,
    ( spl7_4
    | spl7_52
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f1319,f135,f1339,f164])).

fof(f1319,plain,
    ( r2_hidden(sK4(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl7_3 ),
    inference(resolution,[],[f1060,f68])).

fof(f1060,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
        | r2_hidden(X4,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) )
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f1058])).

fof(f1058,plain,
    ( ! [X4] :
        ( r2_hidden(X4,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | r2_hidden(X4,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | ~ r2_hidden(X4,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) )
    | ~ spl7_3 ),
    inference(superposition,[],[f84,f136])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f142,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f141,f135,f127])).

fof(f141,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f105,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f105,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f56,f102,f67,f102])).

fof(f102,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f101])).

fof(f66,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f56,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( r2_hidden(sK1,sK2)
      | r2_hidden(sK0,sK2)
      | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( ~ r2_hidden(sK1,sK2)
        & ~ r2_hidden(sK0,sK2) )
      | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f41])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK1,sK2)
        | r2_hidden(sK0,sK2)
        | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( ~ r2_hidden(sK1,sK2)
          & ~ r2_hidden(sK0,sK2) )
        | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f140,plain,
    ( ~ spl7_2
    | spl7_3 ),
    inference(avatar_split_clause,[],[f139,f135,f131])).

fof(f139,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f104,f63])).

fof(f104,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f57,f102,f67,f102])).

fof(f57,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f138,plain,
    ( spl7_1
    | spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f125,f135,f131,f127])).

fof(f125,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f103,f63])).

fof(f103,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f58,f102,f67,f102])).

fof(f58,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:55:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (21822)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (21816)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (21821)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (21811)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (21813)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (21814)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (21812)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (21827)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (21818)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (21837)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (21815)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (21831)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (21835)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (21836)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (21830)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (21833)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (21813)Refutation not found, incomplete strategy% (21813)------------------------------
% 0.20/0.54  % (21813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (21813)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (21813)Memory used [KB]: 10746
% 0.20/0.54  % (21813)Time elapsed: 0.128 s
% 0.20/0.54  % (21813)------------------------------
% 0.20/0.54  % (21813)------------------------------
% 0.20/0.54  % (21819)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (21820)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (21819)Refutation not found, incomplete strategy% (21819)------------------------------
% 0.20/0.54  % (21819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (21819)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (21819)Memory used [KB]: 10746
% 0.20/0.54  % (21819)Time elapsed: 0.147 s
% 0.20/0.54  % (21819)------------------------------
% 0.20/0.54  % (21819)------------------------------
% 0.20/0.54  % (21834)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (21840)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (21838)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (21829)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (21817)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.55  % (21839)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (21824)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (21832)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (21826)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (21825)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.55  % (21823)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (21828)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.56  % (21828)Refutation not found, incomplete strategy% (21828)------------------------------
% 0.20/0.56  % (21828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (21828)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (21828)Memory used [KB]: 10746
% 0.20/0.56  % (21828)Time elapsed: 0.154 s
% 0.20/0.56  % (21828)------------------------------
% 0.20/0.56  % (21828)------------------------------
% 2.18/0.70  % (21862)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.18/0.72  % (21860)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.86/0.74  % (21861)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.35/0.81  % (21816)Time limit reached!
% 3.35/0.81  % (21816)------------------------------
% 3.35/0.81  % (21816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.35/0.81  % (21816)Termination reason: Time limit
% 3.35/0.81  
% 3.35/0.81  % (21816)Memory used [KB]: 8315
% 3.35/0.81  % (21816)Time elapsed: 0.415 s
% 3.35/0.81  % (21816)------------------------------
% 3.35/0.81  % (21816)------------------------------
% 4.31/0.91  % (21812)Time limit reached!
% 4.31/0.91  % (21812)------------------------------
% 4.31/0.91  % (21812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/0.91  % (21812)Termination reason: Time limit
% 4.31/0.91  % (21812)Termination phase: Saturation
% 4.31/0.91  
% 4.31/0.91  % (21812)Memory used [KB]: 9978
% 4.31/0.91  % (21812)Time elapsed: 0.500 s
% 4.31/0.91  % (21812)------------------------------
% 4.31/0.91  % (21812)------------------------------
% 4.31/0.91  % (21823)Time limit reached!
% 4.31/0.91  % (21823)------------------------------
% 4.31/0.91  % (21823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/0.91  % (21823)Termination reason: Time limit
% 4.31/0.91  
% 4.31/0.91  % (21823)Memory used [KB]: 8315
% 4.31/0.91  % (21823)Time elapsed: 0.518 s
% 4.31/0.91  % (21823)------------------------------
% 4.31/0.91  % (21823)------------------------------
% 4.31/0.92  % (21863)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.31/0.92  % (21821)Time limit reached!
% 4.31/0.92  % (21821)------------------------------
% 4.31/0.92  % (21821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/0.92  % (21821)Termination reason: Time limit
% 4.31/0.92  
% 4.31/0.92  % (21821)Memory used [KB]: 14967
% 4.31/0.92  % (21821)Time elapsed: 0.520 s
% 4.31/0.92  % (21821)------------------------------
% 4.31/0.92  % (21821)------------------------------
% 4.51/0.93  % (21811)Time limit reached!
% 4.51/0.93  % (21811)------------------------------
% 4.51/0.93  % (21811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.51/0.93  % (21811)Termination reason: Time limit
% 4.51/0.93  
% 4.51/0.93  % (21811)Memory used [KB]: 2302
% 4.51/0.93  % (21811)Time elapsed: 0.533 s
% 4.51/0.93  % (21811)------------------------------
% 4.51/0.93  % (21811)------------------------------
% 4.51/1.02  % (21827)Time limit reached!
% 4.51/1.02  % (21827)------------------------------
% 4.51/1.02  % (21827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.51/1.02  % (21827)Termination reason: Time limit
% 4.51/1.02  % (21827)Termination phase: Saturation
% 4.51/1.02  
% 4.51/1.02  % (21827)Memory used [KB]: 16886
% 4.51/1.02  % (21827)Time elapsed: 0.600 s
% 4.51/1.02  % (21827)------------------------------
% 4.51/1.02  % (21827)------------------------------
% 4.51/1.02  % (21818)Time limit reached!
% 4.51/1.02  % (21818)------------------------------
% 4.51/1.02  % (21818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.51/1.02  % (21818)Termination reason: Time limit
% 4.51/1.02  
% 4.51/1.02  % (21818)Memory used [KB]: 10490
% 4.51/1.02  % (21818)Time elapsed: 0.608 s
% 4.51/1.02  % (21818)------------------------------
% 4.51/1.02  % (21818)------------------------------
% 5.16/1.02  % (21839)Time limit reached!
% 5.16/1.02  % (21839)------------------------------
% 5.16/1.02  % (21839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.16/1.02  % (21839)Termination reason: Time limit
% 5.16/1.02  
% 5.16/1.02  % (21839)Memory used [KB]: 9722
% 5.16/1.02  % (21839)Time elapsed: 0.623 s
% 5.16/1.02  % (21839)------------------------------
% 5.16/1.02  % (21839)------------------------------
% 5.16/1.03  % (21864)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.16/1.04  % (21866)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.16/1.05  % (21865)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.52/1.09  % (21867)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.52/1.16  % (21869)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.39/1.17  % (21870)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.39/1.18  % (21868)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.48/1.18  % (21868)Refutation not found, incomplete strategy% (21868)------------------------------
% 6.48/1.18  % (21868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.48/1.18  % (21868)Termination reason: Refutation not found, incomplete strategy
% 6.48/1.18  
% 6.48/1.18  % (21868)Memory used [KB]: 1791
% 6.48/1.18  % (21868)Time elapsed: 0.147 s
% 6.48/1.18  % (21868)------------------------------
% 6.48/1.18  % (21868)------------------------------
% 6.48/1.21  % (21832)Time limit reached!
% 6.48/1.21  % (21832)------------------------------
% 6.48/1.21  % (21832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.48/1.21  % (21832)Termination reason: Time limit
% 6.48/1.21  
% 6.48/1.21  % (21832)Memory used [KB]: 3837
% 6.48/1.21  % (21832)Time elapsed: 0.821 s
% 6.48/1.21  % (21832)------------------------------
% 6.48/1.21  % (21832)------------------------------
% 6.93/1.25  % (21863)Time limit reached!
% 6.93/1.25  % (21863)------------------------------
% 6.93/1.25  % (21863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.93/1.25  % (21863)Termination reason: Time limit
% 6.93/1.25  
% 6.93/1.25  % (21863)Memory used [KB]: 8571
% 6.93/1.25  % (21863)Time elapsed: 0.414 s
% 6.93/1.25  % (21863)------------------------------
% 6.93/1.25  % (21863)------------------------------
% 6.93/1.29  % (21871)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 7.48/1.31  % (21872)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 7.48/1.36  % (21873)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 7.48/1.37  % (21873)Refutation not found, incomplete strategy% (21873)------------------------------
% 7.48/1.37  % (21873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.48/1.37  % (21873)Termination reason: Refutation not found, incomplete strategy
% 7.48/1.37  
% 7.48/1.37  % (21873)Memory used [KB]: 1663
% 7.48/1.37  % (21873)Time elapsed: 0.090 s
% 7.48/1.37  % (21873)------------------------------
% 7.48/1.37  % (21873)------------------------------
% 7.48/1.37  % (21864)Time limit reached!
% 7.48/1.37  % (21864)------------------------------
% 7.48/1.37  % (21864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.98/1.38  % (21864)Termination reason: Time limit
% 7.98/1.38  
% 7.98/1.38  % (21864)Memory used [KB]: 13816
% 7.98/1.38  % (21864)Time elapsed: 0.408 s
% 7.98/1.38  % (21864)------------------------------
% 7.98/1.38  % (21864)------------------------------
% 8.68/1.50  % (21874)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 8.91/1.52  % (21875)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 9.63/1.62  % (21837)Time limit reached!
% 9.63/1.62  % (21837)------------------------------
% 9.63/1.62  % (21837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.63/1.64  % (21837)Termination reason: Time limit
% 9.63/1.64  
% 9.63/1.64  % (21837)Memory used [KB]: 17526
% 9.63/1.64  % (21837)Time elapsed: 1.221 s
% 9.63/1.64  % (21837)------------------------------
% 9.63/1.64  % (21837)------------------------------
% 10.51/1.69  % (21833)Time limit reached!
% 10.51/1.69  % (21833)------------------------------
% 10.51/1.69  % (21833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.51/1.69  % (21833)Termination reason: Time limit
% 10.51/1.69  
% 10.51/1.69  % (21833)Memory used [KB]: 14967
% 10.51/1.69  % (21833)Time elapsed: 1.212 s
% 10.51/1.69  % (21833)------------------------------
% 10.51/1.69  % (21833)------------------------------
% 10.51/1.71  % (21835)Time limit reached!
% 10.51/1.71  % (21835)------------------------------
% 10.51/1.71  % (21835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.51/1.71  % (21835)Termination reason: Time limit
% 10.51/1.71  
% 10.51/1.71  % (21835)Memory used [KB]: 15735
% 10.51/1.71  % (21835)Time elapsed: 1.319 s
% 10.51/1.71  % (21835)------------------------------
% 10.51/1.71  % (21835)------------------------------
% 10.51/1.73  % (21826)Time limit reached!
% 10.51/1.73  % (21826)------------------------------
% 10.51/1.73  % (21826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.51/1.73  % (21826)Termination reason: Time limit
% 10.51/1.73  
% 10.51/1.73  % (21826)Memory used [KB]: 13048
% 10.51/1.73  % (21826)Time elapsed: 1.303 s
% 10.51/1.73  % (21826)------------------------------
% 10.51/1.73  % (21826)------------------------------
% 10.51/1.75  % (21872)Time limit reached!
% 10.51/1.75  % (21872)------------------------------
% 10.51/1.75  % (21872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.51/1.75  % (21872)Termination reason: Time limit
% 10.51/1.75  % (21872)Termination phase: Saturation
% 10.51/1.75  
% 10.51/1.75  % (21872)Memory used [KB]: 4989
% 10.51/1.75  % (21872)Time elapsed: 0.500 s
% 10.51/1.75  % (21872)------------------------------
% 10.51/1.75  % (21872)------------------------------
% 10.51/1.75  % (21875)Refutation found. Thanks to Tanya!
% 10.51/1.75  % SZS status Theorem for theBenchmark
% 10.51/1.75  % SZS output start Proof for theBenchmark
% 10.51/1.75  fof(f4168,plain,(
% 10.51/1.75    $false),
% 10.51/1.75    inference(avatar_sat_refutation,[],[f138,f140,f142,f1342,f1379,f1519,f1616,f1903,f2276,f2283,f2317,f2541,f2566,f2648,f2649,f4158,f4164,f4166,f4167])).
% 10.51/1.75  fof(f4167,plain,(
% 10.51/1.75    sK2 != k3_xboole_0(sK2,sK2) | r2_hidden(sK1,sK2) | ~r2_hidden(sK1,k3_xboole_0(sK2,sK2))),
% 10.51/1.75    introduced(theory_tautology_sat_conflict,[])).
% 10.51/1.75  fof(f4166,plain,(
% 10.51/1.75    sK1 != sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK2 != k3_xboole_0(sK2,sK2) | r2_hidden(sK1,k3_xboole_0(sK2,sK2)) | ~r2_hidden(sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2)),
% 10.51/1.75    introduced(theory_tautology_sat_conflict,[])).
% 10.51/1.75  fof(f4164,plain,(
% 10.51/1.75    sK0 != sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | r2_hidden(sK0,sK2) | ~r2_hidden(sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2)),
% 10.51/1.75    introduced(theory_tautology_sat_conflict,[])).
% 10.51/1.75  fof(f4158,plain,(
% 10.51/1.75    spl7_129 | spl7_130 | ~spl7_11),
% 10.51/1.75    inference(avatar_split_clause,[],[f4149,f365,f4155,f4151])).
% 10.51/1.75  fof(f4151,plain,(
% 10.51/1.75    spl7_129 <=> sK0 = sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 10.51/1.75    introduced(avatar_definition,[new_symbols(naming,[spl7_129])])).
% 10.51/1.75  fof(f4155,plain,(
% 10.51/1.75    spl7_130 <=> sK1 = sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 10.51/1.75    introduced(avatar_definition,[new_symbols(naming,[spl7_130])])).
% 10.51/1.75  fof(f365,plain,(
% 10.51/1.75    spl7_11 <=> r2_hidden(sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 10.51/1.75    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 10.51/1.75  fof(f4149,plain,(
% 10.51/1.75    sK1 = sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK0 = sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl7_11),
% 10.51/1.75    inference(duplicate_literal_removal,[],[f4135])).
% 10.51/1.75  fof(f4135,plain,(
% 10.51/1.75    sK1 = sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK0 = sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK0 = sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl7_11),
% 10.51/1.75    inference(resolution,[],[f367,f124])).
% 10.51/1.75  fof(f124,plain,(
% 10.51/1.75    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 10.51/1.75    inference(equality_resolution,[],[f117])).
% 10.51/1.75  fof(f117,plain,(
% 10.51/1.75    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 10.51/1.75    inference(definition_unfolding,[],[f87,f101])).
% 10.51/1.75  fof(f101,plain,(
% 10.51/1.75    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 10.51/1.75    inference(definition_unfolding,[],[f76,f100])).
% 10.51/1.75  fof(f100,plain,(
% 10.51/1.75    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 10.51/1.75    inference(definition_unfolding,[],[f86,f99])).
% 10.51/1.75  fof(f99,plain,(
% 10.51/1.75    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 10.51/1.75    inference(definition_unfolding,[],[f95,f98])).
% 10.51/1.75  fof(f98,plain,(
% 10.51/1.75    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 10.51/1.75    inference(definition_unfolding,[],[f96,f97])).
% 10.51/1.75  fof(f97,plain,(
% 10.51/1.75    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 10.51/1.75    inference(cnf_transformation,[],[f24])).
% 10.51/1.75  fof(f24,axiom,(
% 10.51/1.75    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 10.51/1.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 10.51/1.75  fof(f96,plain,(
% 10.51/1.75    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 10.51/1.75    inference(cnf_transformation,[],[f23])).
% 10.51/1.75  fof(f23,axiom,(
% 10.51/1.75    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 10.51/1.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 10.51/1.75  fof(f95,plain,(
% 10.51/1.75    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 10.51/1.75    inference(cnf_transformation,[],[f22])).
% 10.51/1.75  fof(f22,axiom,(
% 10.51/1.75    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 10.51/1.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 10.51/1.75  fof(f86,plain,(
% 10.51/1.75    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 10.51/1.75    inference(cnf_transformation,[],[f21])).
% 10.51/1.75  fof(f21,axiom,(
% 10.51/1.75    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 10.51/1.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 10.51/1.75  fof(f76,plain,(
% 10.51/1.75    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 10.51/1.75    inference(cnf_transformation,[],[f20])).
% 10.51/1.75  fof(f20,axiom,(
% 10.51/1.75    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 10.51/1.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 10.51/1.76  fof(f87,plain,(
% 10.51/1.76    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 10.51/1.76    inference(cnf_transformation,[],[f55])).
% 10.51/1.76  fof(f55,plain,(
% 10.51/1.76    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK6(X0,X1,X2,X3) != X2 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X0) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X2 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X0 | r2_hidden(sK6(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 10.51/1.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f53,f54])).
% 10.51/1.76  fof(f54,plain,(
% 10.51/1.76    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK6(X0,X1,X2,X3) != X2 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X0) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X2 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X0 | r2_hidden(sK6(X0,X1,X2,X3),X3))))),
% 10.51/1.76    introduced(choice_axiom,[])).
% 10.51/1.76  fof(f53,plain,(
% 10.51/1.76    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 10.51/1.76    inference(rectify,[],[f52])).
% 10.51/1.76  fof(f52,plain,(
% 10.51/1.76    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 10.51/1.76    inference(flattening,[],[f51])).
% 10.51/1.76  fof(f51,plain,(
% 10.51/1.76    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 10.51/1.76    inference(nnf_transformation,[],[f38])).
% 10.51/1.76  fof(f38,plain,(
% 10.51/1.76    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 10.51/1.76    inference(ennf_transformation,[],[f17])).
% 10.51/1.76  fof(f17,axiom,(
% 10.51/1.76    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 10.51/1.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 10.51/1.76  fof(f367,plain,(
% 10.51/1.76    r2_hidden(sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl7_11),
% 10.51/1.76    inference(avatar_component_clause,[],[f365])).
% 10.51/1.76  fof(f2649,plain,(
% 10.51/1.76    spl7_11 | spl7_4),
% 10.51/1.76    inference(avatar_split_clause,[],[f2640,f164,f365])).
% 10.51/1.76  fof(f164,plain,(
% 10.51/1.76    spl7_4 <=> r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 10.51/1.76    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 10.51/1.76  fof(f2640,plain,(
% 10.51/1.76    r2_hidden(sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | spl7_4),
% 10.51/1.76    inference(resolution,[],[f166,f71])).
% 10.51/1.76  fof(f71,plain,(
% 10.51/1.76    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 10.51/1.76    inference(cnf_transformation,[],[f48])).
% 10.51/1.76  fof(f48,plain,(
% 10.51/1.76    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 10.51/1.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f47])).
% 10.51/1.76  fof(f47,plain,(
% 10.51/1.76    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 10.51/1.76    introduced(choice_axiom,[])).
% 10.51/1.76  fof(f33,plain,(
% 10.51/1.76    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 10.51/1.76    inference(ennf_transformation,[],[f29])).
% 10.51/1.76  fof(f29,plain,(
% 10.51/1.76    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 10.51/1.76    inference(rectify,[],[f5])).
% 10.51/1.77  fof(f5,axiom,(
% 10.51/1.77    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 10.51/1.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 10.51/1.77  fof(f166,plain,(
% 10.51/1.77    ~r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | spl7_4),
% 10.51/1.77    inference(avatar_component_clause,[],[f164])).
% 10.51/1.77  fof(f2648,plain,(
% 10.51/1.77    spl7_10 | spl7_4),
% 10.51/1.77    inference(avatar_split_clause,[],[f2639,f164,f360])).
% 10.51/1.77  fof(f360,plain,(
% 10.51/1.77    spl7_10 <=> r2_hidden(sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2)),
% 10.51/1.77    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 10.51/1.77  fof(f2639,plain,(
% 10.51/1.77    r2_hidden(sK5(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2) | spl7_4),
% 10.51/1.77    inference(resolution,[],[f166,f70])).
% 10.51/1.77  fof(f70,plain,(
% 10.51/1.77    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 10.51/1.77    inference(cnf_transformation,[],[f48])).
% 10.51/1.77  fof(f2566,plain,(
% 10.51/1.77    ~spl7_4 | spl7_3),
% 10.51/1.77    inference(avatar_split_clause,[],[f2565,f135,f164])).
% 10.51/1.77  fof(f135,plain,(
% 10.51/1.77    spl7_3 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 10.51/1.77    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 10.51/1.77  fof(f2565,plain,(
% 10.51/1.77    ~r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | spl7_3),
% 10.51/1.77    inference(trivial_inequality_removal,[],[f2564])).
% 10.51/1.77  fof(f2564,plain,(
% 10.51/1.77    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | ~r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | spl7_3),
% 10.51/1.77    inference(forward_demodulation,[],[f2558,f60])).
% 10.51/1.77  fof(f60,plain,(
% 10.51/1.77    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 10.51/1.77    inference(cnf_transformation,[],[f13])).
% 10.51/1.77  fof(f13,axiom,(
% 10.51/1.77    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 10.51/1.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 10.51/1.77  fof(f2558,plain,(
% 10.51/1.77    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k1_xboole_0) | ~r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | spl7_3),
% 10.51/1.77    inference(superposition,[],[f137,f74])).
% 10.51/1.77  fof(f74,plain,(
% 10.51/1.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 10.51/1.77    inference(cnf_transformation,[],[f49])).
% 10.51/1.77  fof(f49,plain,(
% 10.51/1.77    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 10.51/1.77    inference(nnf_transformation,[],[f3])).
% 10.51/1.77  fof(f3,axiom,(
% 10.51/1.77    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 10.51/1.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 10.51/1.77  fof(f137,plain,(
% 10.51/1.77    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | spl7_3),
% 10.51/1.77    inference(avatar_component_clause,[],[f135])).
% 10.51/1.77  fof(f2541,plain,(
% 10.51/1.77    ~spl7_1 | ~spl7_4),
% 10.51/1.77    inference(avatar_contradiction_clause,[],[f2530])).
% 10.51/1.77  fof(f2530,plain,(
% 10.51/1.77    $false | (~spl7_1 | ~spl7_4)),
% 10.51/1.77    inference(resolution,[],[f1931,f165])).
% 10.51/1.77  fof(f165,plain,(
% 10.51/1.77    r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl7_4),
% 10.51/1.77    inference(avatar_component_clause,[],[f164])).
% 10.51/1.77  fof(f1931,plain,(
% 10.51/1.77    ( ! [X14,X15] : (~r1_xboole_0(sK2,k6_enumset1(X14,X14,X14,X14,X14,X14,sK0,X15))) ) | ~spl7_1),
% 10.51/1.77    inference(resolution,[],[f1909,f121])).
% 10.51/1.77  fof(f121,plain,(
% 10.51/1.77    ( ! [X2,X0,X5] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2))) )),
% 10.51/1.77    inference(equality_resolution,[],[f120])).
% 10.51/1.77  fof(f120,plain,(
% 10.51/1.77    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 10.51/1.77    inference(equality_resolution,[],[f115])).
% 10.51/1.77  fof(f115,plain,(
% 10.51/1.77    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 10.51/1.77    inference(definition_unfolding,[],[f89,f101])).
% 10.51/1.77  fof(f89,plain,(
% 10.51/1.77    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 10.51/1.77    inference(cnf_transformation,[],[f55])).
% 10.51/1.77  fof(f1909,plain,(
% 10.51/1.77    ( ! [X0] : (~r2_hidden(sK0,X0) | ~r1_xboole_0(sK2,X0)) ) | ~spl7_1),
% 10.51/1.77    inference(resolution,[],[f129,f72])).
% 10.51/1.77  fof(f72,plain,(
% 10.51/1.77    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 10.51/1.77    inference(cnf_transformation,[],[f48])).
% 10.51/1.77  fof(f129,plain,(
% 10.51/1.77    r2_hidden(sK0,sK2) | ~spl7_1),
% 10.51/1.77    inference(avatar_component_clause,[],[f127])).
% 10.51/1.77  fof(f127,plain,(
% 10.51/1.77    spl7_1 <=> r2_hidden(sK0,sK2)),
% 10.51/1.77    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 10.51/1.77  fof(f2317,plain,(
% 10.51/1.77    spl7_95 | ~spl7_36),
% 10.51/1.77    inference(avatar_split_clause,[],[f2312,f896,f2314])).
% 10.51/1.77  fof(f2314,plain,(
% 10.51/1.77    spl7_95 <=> sK2 = k3_xboole_0(sK2,sK2)),
% 10.51/1.77    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).
% 10.51/1.77  fof(f896,plain,(
% 10.51/1.77    spl7_36 <=> r1_tarski(sK2,sK2)),
% 10.51/1.77    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 10.51/1.77  fof(f2312,plain,(
% 10.51/1.77    sK2 = k3_xboole_0(sK2,sK2) | ~spl7_36),
% 10.51/1.77    inference(resolution,[],[f897,f73])).
% 10.51/1.77  fof(f73,plain,(
% 10.51/1.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 10.51/1.77    inference(cnf_transformation,[],[f34])).
% 10.51/1.77  fof(f34,plain,(
% 10.51/1.77    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 10.51/1.77    inference(ennf_transformation,[],[f11])).
% 10.51/1.77  fof(f11,axiom,(
% 10.51/1.77    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 10.51/1.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 10.51/1.77  fof(f897,plain,(
% 10.51/1.77    r1_tarski(sK2,sK2) | ~spl7_36),
% 10.51/1.77    inference(avatar_component_clause,[],[f896])).
% 10.51/1.77  fof(f2283,plain,(
% 10.51/1.77    spl7_53 | ~spl7_48),
% 10.51/1.77    inference(avatar_split_clause,[],[f2279,f1277,f1351])).
% 10.51/1.77  fof(f1351,plain,(
% 10.51/1.77    spl7_53 <=> k1_xboole_0 = k3_xboole_0(sK2,k1_xboole_0)),
% 10.51/1.77    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).
% 10.51/1.77  fof(f1277,plain,(
% 10.51/1.77    spl7_48 <=> r1_xboole_0(sK2,k1_xboole_0)),
% 10.51/1.77    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).
% 10.51/1.77  fof(f2279,plain,(
% 10.51/1.77    k1_xboole_0 = k3_xboole_0(sK2,k1_xboole_0) | ~spl7_48),
% 10.51/1.77    inference(resolution,[],[f1279,f74])).
% 10.51/1.77  fof(f1279,plain,(
% 10.51/1.77    r1_xboole_0(sK2,k1_xboole_0) | ~spl7_48),
% 10.51/1.77    inference(avatar_component_clause,[],[f1277])).
% 10.51/1.77  fof(f2276,plain,(
% 10.51/1.77    ~spl7_76),
% 10.51/1.77    inference(avatar_contradiction_clause,[],[f2260])).
% 10.51/1.77  fof(f2260,plain,(
% 10.51/1.77    $false | ~spl7_76),
% 10.51/1.77    inference(resolution,[],[f1684,f1615])).
% 10.51/1.77  fof(f1615,plain,(
% 10.51/1.77    r2_hidden(sK5(sK2,k1_xboole_0),k1_xboole_0) | ~spl7_76),
% 10.51/1.77    inference(avatar_component_clause,[],[f1613])).
% 10.51/1.77  fof(f1613,plain,(
% 10.51/1.77    spl7_76 <=> r2_hidden(sK5(sK2,k1_xboole_0),k1_xboole_0)),
% 10.51/1.77    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).
% 10.51/1.77  fof(f1684,plain,(
% 10.51/1.77    ( ! [X2] : (~r2_hidden(sK5(sK2,k1_xboole_0),X2)) ) | ~spl7_76),
% 10.51/1.77    inference(duplicate_literal_removal,[],[f1683])).
% 10.51/1.77  fof(f1683,plain,(
% 10.51/1.77    ( ! [X2] : (~r2_hidden(sK5(sK2,k1_xboole_0),X2) | ~r2_hidden(sK5(sK2,k1_xboole_0),X2)) ) | ~spl7_76),
% 10.51/1.77    inference(forward_demodulation,[],[f1676,f60])).
% 10.51/1.77  fof(f1676,plain,(
% 10.51/1.77    ( ! [X2] : (~r2_hidden(sK5(sK2,k1_xboole_0),X2) | ~r2_hidden(sK5(sK2,k1_xboole_0),k5_xboole_0(X2,k1_xboole_0))) ) | ~spl7_76),
% 10.51/1.77    inference(resolution,[],[f1615,f82])).
% 10.51/1.77  fof(f82,plain,(
% 10.51/1.77    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 10.51/1.77    inference(cnf_transformation,[],[f50])).
% 10.51/1.77  fof(f50,plain,(
% 10.51/1.77    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 10.51/1.77    inference(nnf_transformation,[],[f37])).
% 10.51/1.77  fof(f37,plain,(
% 10.51/1.77    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 10.51/1.77    inference(ennf_transformation,[],[f4])).
% 10.51/1.77  fof(f4,axiom,(
% 10.51/1.77    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 10.51/1.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 10.51/1.77  fof(f1903,plain,(
% 10.51/1.77    ~spl7_2 | ~spl7_4),
% 10.51/1.77    inference(avatar_contradiction_clause,[],[f1892])).
% 10.51/1.77  fof(f1892,plain,(
% 10.51/1.77    $false | (~spl7_2 | ~spl7_4)),
% 10.51/1.77    inference(resolution,[],[f1074,f165])).
% 10.51/1.77  fof(f1074,plain,(
% 10.51/1.77    ( ! [X12,X13] : (~r1_xboole_0(sK2,k6_enumset1(X12,X12,X12,X12,X12,X12,X13,sK1))) ) | ~spl7_2),
% 10.51/1.77    inference(resolution,[],[f1037,f119])).
% 10.51/1.77  fof(f119,plain,(
% 10.51/1.77    ( ! [X0,X5,X1] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5))) )),
% 10.51/1.77    inference(equality_resolution,[],[f118])).
% 10.51/1.77  fof(f118,plain,(
% 10.51/1.77    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 10.51/1.77    inference(equality_resolution,[],[f114])).
% 10.51/1.77  fof(f114,plain,(
% 10.51/1.77    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 10.51/1.77    inference(definition_unfolding,[],[f90,f101])).
% 10.51/1.77  fof(f90,plain,(
% 10.51/1.77    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 10.51/1.77    inference(cnf_transformation,[],[f55])).
% 10.51/1.77  fof(f1037,plain,(
% 10.51/1.77    ( ! [X0] : (~r2_hidden(sK1,X0) | ~r1_xboole_0(sK2,X0)) ) | ~spl7_2),
% 10.51/1.77    inference(resolution,[],[f133,f72])).
% 10.51/1.77  fof(f133,plain,(
% 10.51/1.77    r2_hidden(sK1,sK2) | ~spl7_2),
% 10.51/1.77    inference(avatar_component_clause,[],[f131])).
% 10.51/1.77  fof(f131,plain,(
% 10.51/1.77    spl7_2 <=> r2_hidden(sK1,sK2)),
% 10.51/1.77    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 10.51/1.77  fof(f1616,plain,(
% 10.51/1.77    spl7_76 | spl7_48),
% 10.51/1.77    inference(avatar_split_clause,[],[f1603,f1277,f1613])).
% 10.51/1.77  fof(f1603,plain,(
% 10.51/1.77    r2_hidden(sK5(sK2,k1_xboole_0),k1_xboole_0) | spl7_48),
% 10.51/1.77    inference(resolution,[],[f1278,f71])).
% 10.51/1.77  fof(f1278,plain,(
% 10.51/1.77    ~r1_xboole_0(sK2,k1_xboole_0) | spl7_48),
% 10.51/1.77    inference(avatar_component_clause,[],[f1277])).
% 10.51/1.77  fof(f1519,plain,(
% 10.51/1.77    spl7_36 | ~spl7_53),
% 10.51/1.77    inference(avatar_split_clause,[],[f1518,f1351,f896])).
% 10.51/1.77  fof(f1518,plain,(
% 10.51/1.77    r1_tarski(sK2,sK2) | ~spl7_53),
% 10.51/1.77    inference(forward_demodulation,[],[f1495,f60])).
% 10.51/1.77  fof(f1495,plain,(
% 10.51/1.77    r1_tarski(k5_xboole_0(sK2,k1_xboole_0),k5_xboole_0(sK2,k1_xboole_0)) | ~spl7_53),
% 10.51/1.77    inference(superposition,[],[f106,f1353])).
% 10.51/1.77  fof(f1353,plain,(
% 10.51/1.77    k1_xboole_0 = k3_xboole_0(sK2,k1_xboole_0) | ~spl7_53),
% 10.51/1.77    inference(avatar_component_clause,[],[f1351])).
% 10.51/1.77  fof(f106,plain,(
% 10.51/1.77    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,X1))) )),
% 10.51/1.77    inference(definition_unfolding,[],[f64,f67])).
% 10.51/1.77  fof(f67,plain,(
% 10.51/1.77    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 10.51/1.77    inference(cnf_transformation,[],[f9])).
% 10.51/1.77  fof(f9,axiom,(
% 10.51/1.77    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 10.51/1.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 10.51/1.77  fof(f64,plain,(
% 10.51/1.77    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 10.51/1.77    inference(cnf_transformation,[],[f16])).
% 10.51/1.77  fof(f16,axiom,(
% 10.51/1.77    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 10.51/1.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).
% 10.51/1.77  fof(f1379,plain,(
% 10.51/1.77    spl7_4 | ~spl7_52 | ~spl7_3),
% 10.51/1.77    inference(avatar_split_clause,[],[f1363,f135,f1339,f164])).
% 10.51/1.77  fof(f1339,plain,(
% 10.51/1.77    spl7_52 <=> r2_hidden(sK4(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 10.51/1.77    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).
% 10.51/1.77  fof(f1363,plain,(
% 10.51/1.77    ~r2_hidden(sK4(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl7_3),
% 10.51/1.77    inference(resolution,[],[f1061,f68])).
% 10.51/1.77  fof(f68,plain,(
% 10.51/1.77    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 10.51/1.77    inference(cnf_transformation,[],[f46])).
% 10.51/1.77  fof(f46,plain,(
% 10.51/1.77    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 10.51/1.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f45])).
% 10.51/1.77  fof(f45,plain,(
% 10.51/1.77    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 10.51/1.77    introduced(choice_axiom,[])).
% 10.51/1.77  fof(f32,plain,(
% 10.51/1.77    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 10.51/1.77    inference(ennf_transformation,[],[f28])).
% 10.51/1.77  fof(f28,plain,(
% 10.51/1.77    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 10.51/1.77    inference(rectify,[],[f6])).
% 10.51/1.77  fof(f6,axiom,(
% 10.51/1.77    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 10.51/1.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 10.51/1.77  fof(f1061,plain,(
% 10.51/1.77    ( ! [X2] : (~r2_hidden(X2,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ) | ~spl7_3),
% 10.51/1.77    inference(duplicate_literal_removal,[],[f1056])).
% 10.51/1.77  fof(f1056,plain,(
% 10.51/1.77    ( ! [X2] : (~r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(X2,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(X2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ) | ~spl7_3),
% 10.51/1.77    inference(superposition,[],[f82,f136])).
% 10.51/1.77  fof(f136,plain,(
% 10.51/1.77    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~spl7_3),
% 10.51/1.77    inference(avatar_component_clause,[],[f135])).
% 10.51/1.77  fof(f1342,plain,(
% 10.51/1.77    spl7_4 | spl7_52 | ~spl7_3),
% 10.51/1.77    inference(avatar_split_clause,[],[f1319,f135,f1339,f164])).
% 10.51/1.77  fof(f1319,plain,(
% 10.51/1.77    r2_hidden(sK4(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl7_3),
% 10.51/1.77    inference(resolution,[],[f1060,f68])).
% 10.51/1.77  fof(f1060,plain,(
% 10.51/1.77    ( ! [X4] : (~r2_hidden(X4,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | r2_hidden(X4,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ) | ~spl7_3),
% 10.51/1.77    inference(duplicate_literal_removal,[],[f1058])).
% 10.51/1.77  fof(f1058,plain,(
% 10.51/1.77    ( ! [X4] : (r2_hidden(X4,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | r2_hidden(X4,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(X4,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ) | ~spl7_3),
% 10.51/1.77    inference(superposition,[],[f84,f136])).
% 10.51/1.77  fof(f84,plain,(
% 10.51/1.77    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 10.51/1.77    inference(cnf_transformation,[],[f50])).
% 10.51/1.77  fof(f142,plain,(
% 10.51/1.77    ~spl7_1 | spl7_3),
% 10.51/1.77    inference(avatar_split_clause,[],[f141,f135,f127])).
% 10.51/1.77  fof(f141,plain,(
% 10.51/1.77    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK0,sK2)),
% 10.51/1.77    inference(forward_demodulation,[],[f105,f63])).
% 10.51/1.77  fof(f63,plain,(
% 10.51/1.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 10.51/1.77    inference(cnf_transformation,[],[f1])).
% 10.51/1.77  fof(f1,axiom,(
% 10.51/1.77    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 10.51/1.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 10.51/1.77  fof(f105,plain,(
% 10.51/1.77    ~r2_hidden(sK0,sK2) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))),
% 10.51/1.77    inference(definition_unfolding,[],[f56,f102,f67,f102])).
% 10.51/1.77  fof(f102,plain,(
% 10.51/1.77    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 10.51/1.77    inference(definition_unfolding,[],[f66,f101])).
% 10.51/1.77  fof(f66,plain,(
% 10.51/1.77    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 10.51/1.77    inference(cnf_transformation,[],[f19])).
% 10.51/1.77  fof(f19,axiom,(
% 10.51/1.77    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 10.51/1.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 10.51/1.77  fof(f56,plain,(
% 10.51/1.77    ~r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 10.51/1.77    inference(cnf_transformation,[],[f42])).
% 10.51/1.77  fof(f42,plain,(
% 10.51/1.77    (r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 10.51/1.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f41])).
% 10.51/1.77  fof(f41,plain,(
% 10.51/1.77    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 10.51/1.77    introduced(choice_axiom,[])).
% 10.51/1.77  fof(f40,plain,(
% 10.51/1.77    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 10.51/1.77    inference(flattening,[],[f39])).
% 10.51/1.77  fof(f39,plain,(
% 10.51/1.77    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 10.51/1.77    inference(nnf_transformation,[],[f30])).
% 10.51/1.77  fof(f30,plain,(
% 10.51/1.77    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 10.51/1.77    inference(ennf_transformation,[],[f27])).
% 10.51/1.77  fof(f27,negated_conjecture,(
% 10.51/1.77    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 10.51/1.77    inference(negated_conjecture,[],[f26])).
% 10.51/1.77  fof(f26,conjecture,(
% 10.51/1.77    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 10.51/1.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 10.51/1.77  fof(f140,plain,(
% 10.51/1.77    ~spl7_2 | spl7_3),
% 10.51/1.77    inference(avatar_split_clause,[],[f139,f135,f131])).
% 10.51/1.77  fof(f139,plain,(
% 10.51/1.77    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK1,sK2)),
% 10.51/1.77    inference(forward_demodulation,[],[f104,f63])).
% 10.51/1.77  fof(f104,plain,(
% 10.51/1.77    ~r2_hidden(sK1,sK2) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))),
% 10.51/1.77    inference(definition_unfolding,[],[f57,f102,f67,f102])).
% 10.51/1.77  fof(f57,plain,(
% 10.51/1.77    ~r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 10.51/1.77    inference(cnf_transformation,[],[f42])).
% 10.51/1.77  fof(f138,plain,(
% 10.51/1.77    spl7_1 | spl7_2 | ~spl7_3),
% 10.51/1.77    inference(avatar_split_clause,[],[f125,f135,f131,f127])).
% 10.51/1.77  fof(f125,plain,(
% 10.51/1.77    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2)),
% 10.51/1.77    inference(forward_demodulation,[],[f103,f63])).
% 10.51/1.77  fof(f103,plain,(
% 10.51/1.77    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))),
% 10.51/1.77    inference(definition_unfolding,[],[f58,f102,f67,f102])).
% 10.51/1.77  fof(f58,plain,(
% 10.51/1.77    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 10.51/1.77    inference(cnf_transformation,[],[f42])).
% 10.51/1.77  % SZS output end Proof for theBenchmark
% 10.51/1.77  % (21875)------------------------------
% 10.51/1.77  % (21875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.51/1.77  % (21875)Termination reason: Refutation
% 10.51/1.77  
% 10.51/1.77  % (21875)Memory used [KB]: 7931
% 10.51/1.77  % (21875)Time elapsed: 0.326 s
% 10.51/1.77  % (21875)------------------------------
% 10.51/1.77  % (21875)------------------------------
% 10.51/1.77  % (21808)Success in time 1.405 s
%------------------------------------------------------------------------------
