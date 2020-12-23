%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:42 EST 2020

% Result     : Theorem 2.17s
% Output     : Refutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 275 expanded)
%              Number of leaves         :   17 (  95 expanded)
%              Depth                    :   13
%              Number of atoms          :  331 (1308 expanded)
%              Number of equality atoms :   47 ( 272 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f395,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f125,f126,f131,f132,f253,f268,f394])).

fof(f394,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f393])).

fof(f393,plain,
    ( $false
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f392,f389])).

fof(f389,plain,
    ( ~ r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl6_1
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f256,f282,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ) ),
    inference(definition_unfolding,[],[f91,f66])).

fof(f66,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f91,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f282,plain,
    ( sK0 != k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))
    | ~ spl6_1
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f254,f115])).

fof(f115,plain,
    ( ! [X2] :
        ( ~ v3_ordinal1(X2)
        | sK0 != k2_xboole_0(X2,k1_tarski(X2)) )
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl6_1
  <=> ! [X2] :
        ( sK0 != k2_xboole_0(X2,k1_tarski(X2))
        | ~ v3_ordinal1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f254,plain,
    ( v3_ordinal1(sK2(sK0))
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f58,f118,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | v3_ordinal1(sK2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ( ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
            & r2_hidden(sK2(X0),X0)
            & v3_ordinal1(sK2(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
        & r2_hidden(sK2(X0),X0)
        & v3_ordinal1(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X1] :
              ( r2_hidden(k1_ordinal1(X1),X0)
              | ~ r2_hidden(X1,X0)
              | ~ v3_ordinal1(X1) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

fof(f118,plain,
    ( ~ v4_ordinal1(sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl6_2
  <=> v4_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f58,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ( v4_ordinal1(sK0)
        & sK0 = k1_ordinal1(sK1)
        & v3_ordinal1(sK1) )
      | ( ! [X2] :
            ( k1_ordinal1(X2) != sK0
            | ~ v3_ordinal1(X2) )
        & ~ v4_ordinal1(sK0) ) )
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ( ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
          | ( ! [X2] :
                ( k1_ordinal1(X2) != X0
                | ~ v3_ordinal1(X2) )
            & ~ v4_ordinal1(X0) ) )
        & v3_ordinal1(X0) )
   => ( ( ( v4_ordinal1(sK0)
          & ? [X1] :
              ( k1_ordinal1(X1) = sK0
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != sK0
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(sK0) ) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( k1_ordinal1(X1) = sK0
        & v3_ordinal1(X1) )
   => ( sK0 = k1_ordinal1(sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ( ( v4_ordinal1(X0)
          & ? [X1] :
              ( k1_ordinal1(X1) = X0
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != X0
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(X0) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X2] :
                  ( v3_ordinal1(X2)
                 => k1_ordinal1(X2) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X1] :
                  ( v3_ordinal1(X1)
                 => k1_ordinal1(X1) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( ~ ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
        & ~ ( ! [X1] :
                ( v3_ordinal1(X1)
               => k1_ordinal1(X1) != X0 )
            & ~ v4_ordinal1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_ordinal1)).

fof(f256,plain,
    ( ~ r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f58,f118,f101])).

fof(f101,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | ~ r2_hidden(k2_xboole_0(sK2(X0),k1_tarski(sK2(X0))),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f71,f66])).

fof(f71,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f392,plain,
    ( r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),k2_xboole_0(sK0,k1_tarski(sK0)))
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f58,f275,f288,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f75,f66])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f288,plain,
    ( r1_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f58,f254,f255,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f72,f66])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f255,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f58,f118,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | r2_hidden(sK2(X0),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f275,plain,
    ( v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))))
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f254,f100])).

fof(f100,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f67,f66])).

fof(f67,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f268,plain,
    ( ~ spl6_3
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f259,f128,f114,f122])).

fof(f122,plain,
    ( spl6_3
  <=> sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f128,plain,
    ( spl6_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f259,plain,
    ( sK0 != k2_xboole_0(sK1,k1_tarski(sK1))
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f130,f115])).

fof(f130,plain,
    ( v3_ordinal1(sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f253,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f246,f111])).

fof(f111,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f246,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f191,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f191,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f187,f124])).

fof(f124,plain,
    ( sK0 = k2_xboole_0(sK1,k1_tarski(sK1))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f122])).

fof(f187,plain,
    ( r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f58,f119,f130,f163,f102])).

fof(f102,plain,(
    ! [X2,X0] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f68,f66])).

fof(f68,plain,(
    ! [X2,X0] :
      ( r2_hidden(k1_ordinal1(X2),X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f163,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl6_3 ),
    inference(superposition,[],[f99,f124])).

fof(f99,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f65,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f119,plain,
    ( v4_ordinal1(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f132,plain,
    ( ~ spl6_2
    | spl6_4 ),
    inference(avatar_split_clause,[],[f59,f128,f117])).

fof(f59,plain,
    ( v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f131,plain,
    ( spl6_1
    | spl6_4 ),
    inference(avatar_split_clause,[],[f98,f128,f114])).

fof(f98,plain,(
    ! [X2] :
      ( v3_ordinal1(sK1)
      | sK0 != k2_xboole_0(X2,k1_tarski(X2))
      | ~ v3_ordinal1(X2) ) ),
    inference(definition_unfolding,[],[f60,f66])).

fof(f60,plain,(
    ! [X2] :
      ( v3_ordinal1(sK1)
      | k1_ordinal1(X2) != sK0
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f126,plain,
    ( ~ spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f97,f122,f117])).

fof(f97,plain,
    ( sK0 = k2_xboole_0(sK1,k1_tarski(sK1))
    | ~ v4_ordinal1(sK0) ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f61,plain,
    ( sK0 = k1_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f125,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f96,f122,f114])).

fof(f96,plain,(
    ! [X2] :
      ( sK0 = k2_xboole_0(sK1,k1_tarski(sK1))
      | sK0 != k2_xboole_0(X2,k1_tarski(X2))
      | ~ v3_ordinal1(X2) ) ),
    inference(definition_unfolding,[],[f62,f66,f66])).

fof(f62,plain,(
    ! [X2] :
      ( sK0 = k1_ordinal1(sK1)
      | k1_ordinal1(X2) != sK0
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f120,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f95,f117,f114])).

fof(f95,plain,(
    ! [X2] :
      ( v4_ordinal1(sK0)
      | sK0 != k2_xboole_0(X2,k1_tarski(X2))
      | ~ v3_ordinal1(X2) ) ),
    inference(definition_unfolding,[],[f64,f66])).

fof(f64,plain,(
    ! [X2] :
      ( v4_ordinal1(sK0)
      | k1_ordinal1(X2) != sK0
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:49:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.46/0.55  % (8335)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.46/0.56  % (8351)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.46/0.57  % (8341)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.66/0.57  % (8336)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.66/0.58  % (8343)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.66/0.59  % (8352)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.66/0.59  % (8344)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.66/0.60  % (8340)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.66/0.60  % (8361)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.66/0.60  % (8362)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.66/0.60  % (8348)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.66/0.60  % (8359)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.66/0.60  % (8339)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.66/0.60  % (8337)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.66/0.61  % (8337)Refutation not found, incomplete strategy% (8337)------------------------------
% 1.66/0.61  % (8337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.61  % (8337)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.61  
% 1.66/0.61  % (8337)Memory used [KB]: 10746
% 1.66/0.61  % (8337)Time elapsed: 0.178 s
% 1.66/0.61  % (8337)------------------------------
% 1.66/0.61  % (8337)------------------------------
% 1.66/0.61  % (8358)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.66/0.61  % (8338)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.66/0.61  % (8357)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.66/0.61  % (8350)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.66/0.62  % (8349)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.66/0.62  % (8363)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.66/0.62  % (8353)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.66/0.63  % (8345)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.66/0.63  % (8356)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.66/0.63  % (8342)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.66/0.63  % (8354)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.66/0.63  % (8357)Refutation not found, incomplete strategy% (8357)------------------------------
% 1.66/0.63  % (8357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.63  % (8357)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.63  
% 1.66/0.63  % (8357)Memory used [KB]: 10746
% 1.66/0.63  % (8357)Time elapsed: 0.193 s
% 1.66/0.63  % (8357)------------------------------
% 1.66/0.63  % (8357)------------------------------
% 1.66/0.63  % (8364)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.66/0.63  % (8355)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.66/0.64  % (8360)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.17/0.64  % (8347)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.17/0.64  % (8346)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.17/0.66  % (8361)Refutation found. Thanks to Tanya!
% 2.17/0.66  % SZS status Theorem for theBenchmark
% 2.17/0.66  % SZS output start Proof for theBenchmark
% 2.17/0.66  fof(f395,plain,(
% 2.17/0.66    $false),
% 2.17/0.66    inference(avatar_sat_refutation,[],[f120,f125,f126,f131,f132,f253,f268,f394])).
% 2.17/0.66  fof(f394,plain,(
% 2.17/0.66    ~spl6_1 | spl6_2),
% 2.17/0.66    inference(avatar_contradiction_clause,[],[f393])).
% 2.17/0.66  fof(f393,plain,(
% 2.17/0.66    $false | (~spl6_1 | spl6_2)),
% 2.17/0.66    inference(subsumption_resolution,[],[f392,f389])).
% 2.17/0.66  fof(f389,plain,(
% 2.17/0.66    ~r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),k2_xboole_0(sK0,k1_tarski(sK0))) | (~spl6_1 | spl6_2)),
% 2.17/0.66    inference(unit_resulting_resolution,[],[f256,f282,f109])).
% 2.17/0.66  fof(f109,plain,(
% 2.17/0.66    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 2.17/0.66    inference(definition_unfolding,[],[f91,f66])).
% 2.17/0.66  fof(f66,plain,(
% 2.17/0.66    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 2.17/0.66    inference(cnf_transformation,[],[f4])).
% 2.17/0.66  fof(f4,axiom,(
% 2.17/0.66    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 2.17/0.66  fof(f91,plain,(
% 2.17/0.66    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 2.17/0.66    inference(cnf_transformation,[],[f57])).
% 2.17/0.66  fof(f57,plain,(
% 2.17/0.66    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 2.17/0.66    inference(flattening,[],[f56])).
% 2.17/0.66  fof(f56,plain,(
% 2.17/0.66    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 2.17/0.66    inference(nnf_transformation,[],[f8])).
% 2.17/0.66  fof(f8,axiom,(
% 2.17/0.66    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 2.17/0.66  fof(f282,plain,(
% 2.17/0.66    sK0 != k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))) | (~spl6_1 | spl6_2)),
% 2.17/0.66    inference(unit_resulting_resolution,[],[f254,f115])).
% 2.17/0.66  fof(f115,plain,(
% 2.17/0.66    ( ! [X2] : (~v3_ordinal1(X2) | sK0 != k2_xboole_0(X2,k1_tarski(X2))) ) | ~spl6_1),
% 2.17/0.66    inference(avatar_component_clause,[],[f114])).
% 2.17/0.66  fof(f114,plain,(
% 2.17/0.66    spl6_1 <=> ! [X2] : (sK0 != k2_xboole_0(X2,k1_tarski(X2)) | ~v3_ordinal1(X2))),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.17/0.66  fof(f254,plain,(
% 2.17/0.66    v3_ordinal1(sK2(sK0)) | spl6_2),
% 2.17/0.66    inference(unit_resulting_resolution,[],[f58,f118,f69])).
% 2.17/0.66  fof(f69,plain,(
% 2.17/0.66    ( ! [X0] : (v4_ordinal1(X0) | v3_ordinal1(sK2(X0)) | ~v3_ordinal1(X0)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f40])).
% 2.17/0.66  fof(f40,plain,(
% 2.17/0.66    ! [X0] : (((v4_ordinal1(X0) | (~r2_hidden(k1_ordinal1(sK2(X0)),X0) & r2_hidden(sK2(X0),X0) & v3_ordinal1(sK2(X0)))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 2.17/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 2.17/0.66  fof(f39,plain,(
% 2.17/0.66    ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK2(X0)),X0) & r2_hidden(sK2(X0),X0) & v3_ordinal1(sK2(X0))))),
% 2.17/0.66    introduced(choice_axiom,[])).
% 2.17/0.66  fof(f38,plain,(
% 2.17/0.66    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 2.17/0.66    inference(rectify,[],[f37])).
% 2.17/0.66  fof(f37,plain,(
% 2.17/0.66    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 2.17/0.66    inference(nnf_transformation,[],[f22])).
% 2.17/0.66  fof(f22,plain,(
% 2.17/0.66    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 2.17/0.66    inference(flattening,[],[f21])).
% 2.17/0.66  fof(f21,plain,(
% 2.17/0.66    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 2.17/0.66    inference(ennf_transformation,[],[f14])).
% 2.17/0.66  fof(f14,axiom,(
% 2.17/0.66    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).
% 2.17/0.66  fof(f118,plain,(
% 2.17/0.66    ~v4_ordinal1(sK0) | spl6_2),
% 2.17/0.66    inference(avatar_component_clause,[],[f117])).
% 2.17/0.66  fof(f117,plain,(
% 2.17/0.66    spl6_2 <=> v4_ordinal1(sK0)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.17/0.66  fof(f58,plain,(
% 2.17/0.66    v3_ordinal1(sK0)),
% 2.17/0.66    inference(cnf_transformation,[],[f36])).
% 2.17/0.66  fof(f36,plain,(
% 2.17/0.66    ((v4_ordinal1(sK0) & (sK0 = k1_ordinal1(sK1) & v3_ordinal1(sK1))) | (! [X2] : (k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK0))) & v3_ordinal1(sK0)),
% 2.17/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f35,f34])).
% 2.17/0.66  fof(f34,plain,(
% 2.17/0.66    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0)) => (((v4_ordinal1(sK0) & ? [X1] : (k1_ordinal1(X1) = sK0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK0))) & v3_ordinal1(sK0))),
% 2.17/0.66    introduced(choice_axiom,[])).
% 2.17/0.66  fof(f35,plain,(
% 2.17/0.66    ? [X1] : (k1_ordinal1(X1) = sK0 & v3_ordinal1(X1)) => (sK0 = k1_ordinal1(sK1) & v3_ordinal1(sK1))),
% 2.17/0.66    introduced(choice_axiom,[])).
% 2.17/0.66  fof(f19,plain,(
% 2.17/0.66    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 2.17/0.66    inference(ennf_transformation,[],[f18])).
% 2.17/0.66  fof(f18,plain,(
% 2.17/0.66    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X2] : (v3_ordinal1(X2) => k1_ordinal1(X2) != X0) & ~v4_ordinal1(X0))))),
% 2.17/0.66    inference(rectify,[],[f17])).
% 2.17/0.66  fof(f17,negated_conjecture,(
% 2.17/0.66    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 2.17/0.66    inference(negated_conjecture,[],[f16])).
% 2.17/0.66  fof(f16,conjecture,(
% 2.17/0.66    ! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_ordinal1)).
% 2.17/0.66  fof(f256,plain,(
% 2.17/0.66    ~r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0) | spl6_2),
% 2.17/0.66    inference(unit_resulting_resolution,[],[f58,f118,f101])).
% 2.17/0.66  fof(f101,plain,(
% 2.17/0.66    ( ! [X0] : (v4_ordinal1(X0) | ~r2_hidden(k2_xboole_0(sK2(X0),k1_tarski(sK2(X0))),X0) | ~v3_ordinal1(X0)) )),
% 2.17/0.66    inference(definition_unfolding,[],[f71,f66])).
% 2.17/0.66  fof(f71,plain,(
% 2.17/0.66    ( ! [X0] : (v4_ordinal1(X0) | ~r2_hidden(k1_ordinal1(sK2(X0)),X0) | ~v3_ordinal1(X0)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f40])).
% 2.17/0.66  fof(f392,plain,(
% 2.17/0.66    r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),k2_xboole_0(sK0,k1_tarski(sK0))) | spl6_2),
% 2.17/0.66    inference(unit_resulting_resolution,[],[f58,f275,f288,f105])).
% 2.17/0.66  fof(f105,plain,(
% 2.17/0.66    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.17/0.66    inference(definition_unfolding,[],[f75,f66])).
% 2.17/0.66  fof(f75,plain,(
% 2.17/0.66    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f42])).
% 2.17/0.66  fof(f42,plain,(
% 2.17/0.66    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.17/0.66    inference(nnf_transformation,[],[f24])).
% 2.17/0.66  fof(f24,plain,(
% 2.17/0.66    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.17/0.66    inference(ennf_transformation,[],[f12])).
% 2.17/0.66  fof(f12,axiom,(
% 2.17/0.66    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 2.17/0.66  fof(f288,plain,(
% 2.17/0.66    r1_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0) | spl6_2),
% 2.17/0.66    inference(unit_resulting_resolution,[],[f58,f254,f255,f104])).
% 2.17/0.66  fof(f104,plain,(
% 2.17/0.66    ( ! [X0,X1] : (r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.17/0.66    inference(definition_unfolding,[],[f72,f66])).
% 2.17/0.66  fof(f72,plain,(
% 2.17/0.66    ( ! [X0,X1] : (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f41])).
% 2.17/0.66  fof(f41,plain,(
% 2.17/0.66    ! [X0] : (! [X1] : (((r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.17/0.66    inference(nnf_transformation,[],[f23])).
% 2.17/0.66  fof(f23,plain,(
% 2.17/0.66    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.17/0.66    inference(ennf_transformation,[],[f11])).
% 2.17/0.66  fof(f11,axiom,(
% 2.17/0.66    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 2.17/0.66  fof(f255,plain,(
% 2.17/0.66    r2_hidden(sK2(sK0),sK0) | spl6_2),
% 2.17/0.66    inference(unit_resulting_resolution,[],[f58,f118,f70])).
% 2.17/0.66  fof(f70,plain,(
% 2.17/0.66    ( ! [X0] : (v4_ordinal1(X0) | r2_hidden(sK2(X0),X0) | ~v3_ordinal1(X0)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f40])).
% 2.17/0.66  fof(f275,plain,(
% 2.17/0.66    v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))) | spl6_2),
% 2.17/0.66    inference(unit_resulting_resolution,[],[f254,f100])).
% 2.17/0.66  fof(f100,plain,(
% 2.17/0.66    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 2.17/0.66    inference(definition_unfolding,[],[f67,f66])).
% 2.17/0.66  fof(f67,plain,(
% 2.17/0.66    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f20])).
% 2.17/0.66  fof(f20,plain,(
% 2.17/0.66    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 2.17/0.66    inference(ennf_transformation,[],[f10])).
% 2.17/0.66  fof(f10,axiom,(
% 2.17/0.66    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 2.17/0.66  fof(f268,plain,(
% 2.17/0.66    ~spl6_3 | ~spl6_1 | ~spl6_4),
% 2.17/0.66    inference(avatar_split_clause,[],[f259,f128,f114,f122])).
% 2.17/0.66  fof(f122,plain,(
% 2.17/0.66    spl6_3 <=> sK0 = k2_xboole_0(sK1,k1_tarski(sK1))),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.17/0.66  fof(f128,plain,(
% 2.17/0.66    spl6_4 <=> v3_ordinal1(sK1)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.17/0.66  fof(f259,plain,(
% 2.17/0.66    sK0 != k2_xboole_0(sK1,k1_tarski(sK1)) | (~spl6_1 | ~spl6_4)),
% 2.17/0.66    inference(unit_resulting_resolution,[],[f130,f115])).
% 2.17/0.66  fof(f130,plain,(
% 2.17/0.66    v3_ordinal1(sK1) | ~spl6_4),
% 2.17/0.66    inference(avatar_component_clause,[],[f128])).
% 2.17/0.66  fof(f253,plain,(
% 2.17/0.66    ~spl6_2 | ~spl6_3 | ~spl6_4),
% 2.17/0.66    inference(avatar_contradiction_clause,[],[f252])).
% 2.17/0.66  fof(f252,plain,(
% 2.17/0.66    $false | (~spl6_2 | ~spl6_3 | ~spl6_4)),
% 2.17/0.66    inference(subsumption_resolution,[],[f246,f111])).
% 2.17/0.66  fof(f111,plain,(
% 2.17/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.17/0.66    inference(equality_resolution,[],[f85])).
% 2.17/0.66  fof(f85,plain,(
% 2.17/0.66    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.17/0.66    inference(cnf_transformation,[],[f51])).
% 2.17/0.66  fof(f51,plain,(
% 2.17/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.17/0.66    inference(flattening,[],[f50])).
% 2.17/0.66  fof(f50,plain,(
% 2.17/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.17/0.66    inference(nnf_transformation,[],[f2])).
% 2.17/0.66  fof(f2,axiom,(
% 2.17/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.17/0.66  fof(f246,plain,(
% 2.17/0.66    ~r1_tarski(sK0,sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4)),
% 2.17/0.66    inference(unit_resulting_resolution,[],[f191,f94])).
% 2.17/0.66  fof(f94,plain,(
% 2.17/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f33])).
% 2.17/0.66  fof(f33,plain,(
% 2.17/0.66    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.17/0.66    inference(ennf_transformation,[],[f15])).
% 2.17/0.66  fof(f15,axiom,(
% 2.17/0.66    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.17/0.66  fof(f191,plain,(
% 2.17/0.66    r2_hidden(sK0,sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4)),
% 2.17/0.66    inference(forward_demodulation,[],[f187,f124])).
% 2.17/0.66  fof(f124,plain,(
% 2.17/0.66    sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) | ~spl6_3),
% 2.17/0.66    inference(avatar_component_clause,[],[f122])).
% 2.17/0.66  fof(f187,plain,(
% 2.17/0.66    r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4)),
% 2.17/0.66    inference(unit_resulting_resolution,[],[f58,f119,f130,f163,f102])).
% 2.17/0.66  fof(f102,plain,(
% 2.17/0.66    ( ! [X2,X0] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | ~v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 2.17/0.66    inference(definition_unfolding,[],[f68,f66])).
% 2.17/0.66  fof(f68,plain,(
% 2.17/0.66    ( ! [X2,X0] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | ~v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f40])).
% 2.17/0.66  fof(f163,plain,(
% 2.17/0.66    r2_hidden(sK1,sK0) | ~spl6_3),
% 2.17/0.66    inference(superposition,[],[f99,f124])).
% 2.17/0.66  fof(f99,plain,(
% 2.17/0.66    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 2.17/0.66    inference(definition_unfolding,[],[f65,f66])).
% 2.17/0.66  fof(f65,plain,(
% 2.17/0.66    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 2.17/0.66    inference(cnf_transformation,[],[f7])).
% 2.17/0.66  fof(f7,axiom,(
% 2.17/0.66    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 2.17/0.66  fof(f119,plain,(
% 2.17/0.66    v4_ordinal1(sK0) | ~spl6_2),
% 2.17/0.66    inference(avatar_component_clause,[],[f117])).
% 2.17/0.66  fof(f132,plain,(
% 2.17/0.66    ~spl6_2 | spl6_4),
% 2.17/0.66    inference(avatar_split_clause,[],[f59,f128,f117])).
% 2.17/0.66  fof(f59,plain,(
% 2.17/0.66    v3_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 2.17/0.66    inference(cnf_transformation,[],[f36])).
% 2.17/0.66  fof(f131,plain,(
% 2.17/0.66    spl6_1 | spl6_4),
% 2.17/0.66    inference(avatar_split_clause,[],[f98,f128,f114])).
% 2.17/0.66  fof(f98,plain,(
% 2.17/0.66    ( ! [X2] : (v3_ordinal1(sK1) | sK0 != k2_xboole_0(X2,k1_tarski(X2)) | ~v3_ordinal1(X2)) )),
% 2.17/0.66    inference(definition_unfolding,[],[f60,f66])).
% 2.17/0.66  fof(f60,plain,(
% 2.17/0.66    ( ! [X2] : (v3_ordinal1(sK1) | k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f36])).
% 2.17/0.66  fof(f126,plain,(
% 2.17/0.66    ~spl6_2 | spl6_3),
% 2.17/0.66    inference(avatar_split_clause,[],[f97,f122,f117])).
% 2.17/0.66  fof(f97,plain,(
% 2.17/0.66    sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) | ~v4_ordinal1(sK0)),
% 2.17/0.66    inference(definition_unfolding,[],[f61,f66])).
% 2.17/0.66  fof(f61,plain,(
% 2.17/0.66    sK0 = k1_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 2.17/0.66    inference(cnf_transformation,[],[f36])).
% 2.17/0.66  fof(f125,plain,(
% 2.17/0.66    spl6_1 | spl6_3),
% 2.17/0.66    inference(avatar_split_clause,[],[f96,f122,f114])).
% 2.17/0.66  fof(f96,plain,(
% 2.17/0.66    ( ! [X2] : (sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) | sK0 != k2_xboole_0(X2,k1_tarski(X2)) | ~v3_ordinal1(X2)) )),
% 2.17/0.66    inference(definition_unfolding,[],[f62,f66,f66])).
% 2.17/0.66  fof(f62,plain,(
% 2.17/0.66    ( ! [X2] : (sK0 = k1_ordinal1(sK1) | k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f36])).
% 2.17/0.66  fof(f120,plain,(
% 2.17/0.66    spl6_1 | spl6_2),
% 2.17/0.66    inference(avatar_split_clause,[],[f95,f117,f114])).
% 2.17/0.66  fof(f95,plain,(
% 2.17/0.66    ( ! [X2] : (v4_ordinal1(sK0) | sK0 != k2_xboole_0(X2,k1_tarski(X2)) | ~v3_ordinal1(X2)) )),
% 2.17/0.66    inference(definition_unfolding,[],[f64,f66])).
% 2.17/0.66  fof(f64,plain,(
% 2.17/0.66    ( ! [X2] : (v4_ordinal1(sK0) | k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f36])).
% 2.17/0.66  % SZS output end Proof for theBenchmark
% 2.17/0.66  % (8361)------------------------------
% 2.17/0.66  % (8361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.66  % (8361)Termination reason: Refutation
% 2.17/0.66  
% 2.17/0.66  % (8361)Memory used [KB]: 10874
% 2.17/0.66  % (8361)Time elapsed: 0.235 s
% 2.17/0.66  % (8361)------------------------------
% 2.17/0.66  % (8361)------------------------------
% 2.17/0.66  % (8334)Success in time 0.297 s
%------------------------------------------------------------------------------
