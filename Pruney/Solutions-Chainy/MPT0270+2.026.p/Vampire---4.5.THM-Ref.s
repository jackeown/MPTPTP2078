%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:59 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 147 expanded)
%              Number of leaves         :   12 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  313 ( 682 expanded)
%              Number of equality atoms :  129 ( 218 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f462,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f110,f407,f461])).

fof(f461,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f460])).

fof(f460,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f459,f95])).

fof(f95,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f67,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f39])).

% (19621)Termination reason: Refutation not found, incomplete strategy

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).

fof(f38,plain,(
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
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f459,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(superposition,[],[f408,f103])).

fof(f103,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_1
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f408,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(X0,sK1))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f108,f92])).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f108,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f407,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f405,f371])).

fof(f371,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_1 ),
    inference(duplicate_literal_removal,[],[f370])).

fof(f370,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_1 ),
    inference(equality_resolution,[],[f166])).

fof(f166,plain,
    ( ! [X0] :
        ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X0),k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X0),X0) )
    | spl5_1 ),
    inference(superposition,[],[f104,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f104,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f405,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f403,f340])).

fof(f340,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1)
    | spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f338,f259])).

fof(f259,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X4,k2_enumset1(sK0,sK0,sK0,sK0)) )
    | spl5_2 ),
    inference(superposition,[],[f92,f115])).

fof(f115,plain,
    ( sK1 = k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f107,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f56,f73])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f57])).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f107,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f338,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_1 ),
    inference(equality_resolution,[],[f167])).

fof(f167,plain,
    ( ! [X1] :
        ( k2_enumset1(sK0,sK0,sK0,sK0) != X1
        | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X1),sK1)
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X1),X1) )
    | spl5_1 ),
    inference(superposition,[],[f104,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f403,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1)
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_1 ),
    inference(duplicate_literal_removal,[],[f402])).

fof(f402,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1)
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_1 ),
    inference(equality_resolution,[],[f168])).

fof(f168,plain,
    ( ! [X2] :
        ( k2_enumset1(sK0,sK0,sK0,sK0) != X2
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X2),sK1)
        | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X2),k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X2),X2) )
    | spl5_1 ),
    inference(superposition,[],[f104,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f110,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f76,f106,f102])).

fof(f76,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f40,f73,f73])).

fof(f40,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( r2_hidden(sK0,sK1)
      | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( ~ r2_hidden(sK0,sK1)
      | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X0,X1)
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
        & ( ~ r2_hidden(X0,X1)
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( r2_hidden(sK0,sK1)
        | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( ~ r2_hidden(sK0,sK1)
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f109,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f75,f106,f102])).

fof(f75,plain,
    ( r2_hidden(sK0,sK1)
    | k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f41,f73,f73])).

fof(f41,plain,
    ( r2_hidden(sK0,sK1)
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:22:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (19612)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (19604)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (19608)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (19609)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (19628)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (19610)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (19627)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.55  % (19615)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.55  % (19626)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.41/0.55  % (19619)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.55  % (19614)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.55  % (19607)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.41/0.55  % (19625)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.55  % (19611)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.55  % (19618)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.41/0.56  % (19617)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.56  % (19624)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.56  % (19623)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.56  % (19629)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.56  % (19620)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.56  % (19605)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.60/0.56  % (19632)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.60/0.57  % (19613)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.60/0.57  % (19633)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.60/0.57  % (19631)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.60/0.57  % (19616)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.60/0.57  % (19606)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.60/0.57  % (19630)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.60/0.59  % (19622)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.60/0.60  % (19621)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.60/0.60  % (19621)Refutation not found, incomplete strategy% (19621)------------------------------
% 1.60/0.60  % (19621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.60  % (19630)Refutation found. Thanks to Tanya!
% 1.60/0.60  % SZS status Theorem for theBenchmark
% 1.60/0.60  % SZS output start Proof for theBenchmark
% 1.60/0.60  fof(f462,plain,(
% 1.60/0.60    $false),
% 1.60/0.60    inference(avatar_sat_refutation,[],[f109,f110,f407,f461])).
% 1.60/0.60  fof(f461,plain,(
% 1.60/0.60    ~spl5_1 | ~spl5_2),
% 1.60/0.60    inference(avatar_contradiction_clause,[],[f460])).
% 1.60/0.60  fof(f460,plain,(
% 1.60/0.60    $false | (~spl5_1 | ~spl5_2)),
% 1.60/0.60    inference(subsumption_resolution,[],[f459,f95])).
% 1.60/0.60  fof(f95,plain,(
% 1.60/0.60    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 1.60/0.60    inference(equality_resolution,[],[f94])).
% 1.60/0.60  fof(f94,plain,(
% 1.60/0.60    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 1.60/0.60    inference(equality_resolution,[],[f85])).
% 1.60/0.60  fof(f85,plain,(
% 1.60/0.60    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.60/0.60    inference(definition_unfolding,[],[f67,f57])).
% 1.60/0.60  fof(f57,plain,(
% 1.60/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f12])).
% 1.60/0.60  fof(f12,axiom,(
% 1.60/0.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.60/0.60  fof(f67,plain,(
% 1.60/0.60    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.60/0.60    inference(cnf_transformation,[],[f39])).
% 1.60/0.60  % (19621)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.60  
% 1.60/0.60  fof(f39,plain,(
% 1.60/0.60    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.60/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).
% 1.60/0.60  fof(f38,plain,(
% 1.60/0.60    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.60/0.60    introduced(choice_axiom,[])).
% 1.60/0.60  fof(f37,plain,(
% 1.60/0.60    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.60/0.60    inference(rectify,[],[f36])).
% 1.60/0.60  fof(f36,plain,(
% 1.60/0.60    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.60/0.60    inference(flattening,[],[f35])).
% 1.60/0.60  fof(f35,plain,(
% 1.60/0.60    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.60/0.60    inference(nnf_transformation,[],[f19])).
% 1.60/0.61  fof(f19,plain,(
% 1.60/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.60/0.61    inference(ennf_transformation,[],[f9])).
% 1.60/0.61  fof(f9,axiom,(
% 1.60/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.60/0.61  fof(f459,plain,(
% 1.60/0.61    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl5_1 | ~spl5_2)),
% 1.60/0.61    inference(superposition,[],[f408,f103])).
% 1.60/0.61  fof(f103,plain,(
% 1.60/0.61    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl5_1),
% 1.60/0.61    inference(avatar_component_clause,[],[f102])).
% 1.60/0.61  fof(f102,plain,(
% 1.60/0.61    spl5_1 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.60/0.61  fof(f408,plain,(
% 1.60/0.61    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(X0,sK1))) ) | ~spl5_2),
% 1.60/0.61    inference(unit_resulting_resolution,[],[f108,f92])).
% 1.60/0.61  fof(f92,plain,(
% 1.60/0.61    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.60/0.61    inference(equality_resolution,[],[f59])).
% 1.60/0.61  fof(f59,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.60/0.61    inference(cnf_transformation,[],[f34])).
% 1.60/0.61  fof(f34,plain,(
% 1.60/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.60/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 1.60/0.61  fof(f33,plain,(
% 1.60/0.61    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.60/0.61    introduced(choice_axiom,[])).
% 1.60/0.61  fof(f32,plain,(
% 1.60/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.60/0.61    inference(rectify,[],[f31])).
% 1.60/0.61  fof(f31,plain,(
% 1.60/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.60/0.61    inference(flattening,[],[f30])).
% 1.60/0.61  fof(f30,plain,(
% 1.60/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.60/0.61    inference(nnf_transformation,[],[f3])).
% 1.60/0.61  fof(f3,axiom,(
% 1.60/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.60/0.61  fof(f108,plain,(
% 1.60/0.61    r2_hidden(sK0,sK1) | ~spl5_2),
% 1.60/0.61    inference(avatar_component_clause,[],[f106])).
% 1.60/0.61  fof(f106,plain,(
% 1.60/0.61    spl5_2 <=> r2_hidden(sK0,sK1)),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.60/0.61  fof(f407,plain,(
% 1.60/0.61    spl5_1 | spl5_2),
% 1.60/0.61    inference(avatar_contradiction_clause,[],[f406])).
% 1.60/0.61  fof(f406,plain,(
% 1.60/0.61    $false | (spl5_1 | spl5_2)),
% 1.60/0.61    inference(subsumption_resolution,[],[f405,f371])).
% 1.60/0.61  fof(f371,plain,(
% 1.60/0.61    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_1),
% 1.60/0.61    inference(duplicate_literal_removal,[],[f370])).
% 1.60/0.61  fof(f370,plain,(
% 1.60/0.61    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_1),
% 1.60/0.61    inference(equality_resolution,[],[f166])).
% 1.60/0.61  fof(f166,plain,(
% 1.60/0.61    ( ! [X0] : (k2_enumset1(sK0,sK0,sK0,sK0) != X0 | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X0),k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X0),X0)) ) | spl5_1),
% 1.60/0.61    inference(superposition,[],[f104,f61])).
% 1.60/0.61  fof(f61,plain,(
% 1.60/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f34])).
% 1.60/0.61  fof(f104,plain,(
% 1.60/0.61    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl5_1),
% 1.60/0.61    inference(avatar_component_clause,[],[f102])).
% 1.60/0.61  fof(f405,plain,(
% 1.60/0.61    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | (spl5_1 | spl5_2)),
% 1.60/0.61    inference(subsumption_resolution,[],[f403,f340])).
% 1.60/0.61  fof(f340,plain,(
% 1.60/0.61    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1) | (spl5_1 | spl5_2)),
% 1.60/0.61    inference(subsumption_resolution,[],[f338,f259])).
% 1.60/0.61  fof(f259,plain,(
% 1.60/0.61    ( ! [X4] : (~r2_hidden(X4,sK1) | ~r2_hidden(X4,k2_enumset1(sK0,sK0,sK0,sK0))) ) | spl5_2),
% 1.60/0.61    inference(superposition,[],[f92,f115])).
% 1.60/0.61  fof(f115,plain,(
% 1.60/0.61    sK1 = k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_2),
% 1.60/0.61    inference(unit_resulting_resolution,[],[f107,f79])).
% 1.60/0.61  fof(f79,plain,(
% 1.60/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.60/0.61    inference(definition_unfolding,[],[f56,f73])).
% 1.60/0.61  fof(f73,plain,(
% 1.60/0.61    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.60/0.61    inference(definition_unfolding,[],[f42,f72])).
% 1.60/0.61  fof(f72,plain,(
% 1.60/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.60/0.61    inference(definition_unfolding,[],[f45,f57])).
% 1.60/0.61  fof(f45,plain,(
% 1.60/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f11])).
% 1.60/0.61  fof(f11,axiom,(
% 1.60/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.60/0.61  fof(f42,plain,(
% 1.60/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f10])).
% 1.60/0.61  fof(f10,axiom,(
% 1.60/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.60/0.61  fof(f56,plain,(
% 1.60/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f29])).
% 1.60/0.61  fof(f29,plain,(
% 1.60/0.61    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.60/0.61    inference(nnf_transformation,[],[f13])).
% 1.60/0.61  fof(f13,axiom,(
% 1.60/0.61    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.60/0.61  fof(f107,plain,(
% 1.60/0.61    ~r2_hidden(sK0,sK1) | spl5_2),
% 1.60/0.61    inference(avatar_component_clause,[],[f106])).
% 1.60/0.61  fof(f338,plain,(
% 1.60/0.61    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_1),
% 1.60/0.61    inference(equality_resolution,[],[f167])).
% 1.60/0.61  fof(f167,plain,(
% 1.60/0.61    ( ! [X1] : (k2_enumset1(sK0,sK0,sK0,sK0) != X1 | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X1),sK1) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X1),X1)) ) | spl5_1),
% 1.60/0.61    inference(superposition,[],[f104,f62])).
% 1.60/0.61  fof(f62,plain,(
% 1.60/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f34])).
% 1.60/0.61  fof(f403,plain,(
% 1.60/0.61    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_1),
% 1.60/0.61    inference(duplicate_literal_removal,[],[f402])).
% 1.60/0.61  fof(f402,plain,(
% 1.60/0.61    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_1),
% 1.60/0.61    inference(equality_resolution,[],[f168])).
% 1.60/0.61  fof(f168,plain,(
% 1.60/0.61    ( ! [X2] : (k2_enumset1(sK0,sK0,sK0,sK0) != X2 | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X2),sK1) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X2),k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK0),sK1,X2),X2)) ) | spl5_1),
% 1.60/0.61    inference(superposition,[],[f104,f63])).
% 1.60/0.61  fof(f63,plain,(
% 1.60/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f34])).
% 1.60/0.61  fof(f110,plain,(
% 1.60/0.61    spl5_1 | ~spl5_2),
% 1.60/0.61    inference(avatar_split_clause,[],[f76,f106,f102])).
% 1.60/0.61  fof(f76,plain,(
% 1.60/0.61    ~r2_hidden(sK0,sK1) | k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.60/0.61    inference(definition_unfolding,[],[f40,f73,f73])).
% 1.60/0.61  fof(f40,plain,(
% 1.60/0.61    ~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.60/0.61    inference(cnf_transformation,[],[f22])).
% 1.60/0.61  fof(f22,plain,(
% 1.60/0.61    (r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)) & (~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1))),
% 1.60/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).
% 1.60/0.61  fof(f21,plain,(
% 1.60/0.61    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1))) => ((r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)) & (~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 1.60/0.61    introduced(choice_axiom,[])).
% 1.60/0.61  fof(f20,plain,(
% 1.60/0.61    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)))),
% 1.60/0.61    inference(nnf_transformation,[],[f16])).
% 1.60/0.61  fof(f16,plain,(
% 1.60/0.61    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 1.60/0.61    inference(ennf_transformation,[],[f15])).
% 1.60/0.61  fof(f15,negated_conjecture,(
% 1.60/0.61    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.60/0.61    inference(negated_conjecture,[],[f14])).
% 1.60/0.61  fof(f14,conjecture,(
% 1.60/0.61    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 1.60/0.61  fof(f109,plain,(
% 1.60/0.61    ~spl5_1 | spl5_2),
% 1.60/0.61    inference(avatar_split_clause,[],[f75,f106,f102])).
% 1.60/0.61  fof(f75,plain,(
% 1.60/0.61    r2_hidden(sK0,sK1) | k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.60/0.61    inference(definition_unfolding,[],[f41,f73,f73])).
% 1.60/0.61  fof(f41,plain,(
% 1.60/0.61    r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.60/0.61    inference(cnf_transformation,[],[f22])).
% 1.60/0.61  % SZS output end Proof for theBenchmark
% 1.60/0.61  % (19630)------------------------------
% 1.60/0.61  % (19630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.61  % (19630)Termination reason: Refutation
% 1.60/0.61  
% 1.60/0.61  % (19630)Memory used [KB]: 11001
% 1.60/0.61  % (19630)Time elapsed: 0.200 s
% 1.60/0.61  % (19630)------------------------------
% 1.60/0.61  % (19630)------------------------------
% 1.60/0.61  % (19621)Memory used [KB]: 10618
% 1.60/0.61  % (19621)Time elapsed: 0.163 s
% 1.60/0.61  % (19621)------------------------------
% 1.60/0.61  % (19621)------------------------------
% 1.60/0.63  % (19603)Success in time 0.266 s
%------------------------------------------------------------------------------
