%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 451 expanded)
%              Number of leaves         :   22 ( 143 expanded)
%              Depth                    :   19
%              Number of atoms          :  504 (1827 expanded)
%              Number of equality atoms :   62 ( 393 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f643,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f89,f90,f96,f247,f250,f276,f303,f329,f604,f642])).

fof(f642,plain,
    ( ~ spl4_3
    | spl4_26 ),
    inference(avatar_contradiction_clause,[],[f641])).

fof(f641,plain,
    ( $false
    | ~ spl4_3
    | spl4_26 ),
    inference(subsumption_resolution,[],[f640,f579])).

fof(f579,plain,
    ( sK1 != sK3(sK1,sK0)
    | spl4_26 ),
    inference(avatar_component_clause,[],[f578])).

fof(f578,plain,
    ( spl4_26
  <=> sK1 = sK3(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f640,plain,
    ( sK1 = sK3(sK1,sK0)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f639,f540])).

fof(f540,plain,
    ( r2_hidden(sK3(sK1,sK0),sK0)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f528,f340])).

fof(f340,plain,
    ( sK0 != sK1
    | ~ spl4_3 ),
    inference(superposition,[],[f65,f88])).

fof(f88,plain,
    ( sK0 = k2_xboole_0(sK1,k1_tarski(sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_3
  <=> sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f65,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) != X0 ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f45,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f44,plain,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

fof(f528,plain,
    ( r2_hidden(sK3(sK1,sK0),sK0)
    | sK0 = sK1
    | ~ spl4_3 ),
    inference(factoring,[],[f360])).

fof(f360,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(sK1,X1),sK0)
        | r2_hidden(sK3(sK1,X1),X1)
        | sK1 = X1 )
    | ~ spl4_3 ),
    inference(resolution,[],[f344,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f344,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | r2_hidden(X2,sK0) )
    | ~ spl4_3 ),
    inference(superposition,[],[f74,f88])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f45])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f639,plain,
    ( ~ r2_hidden(sK3(sK1,sK0),sK0)
    | sK1 = sK3(sK1,sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f572,f345])).

fof(f345,plain,
    ( ! [X3] :
        ( r2_hidden(X3,sK1)
        | ~ r2_hidden(X3,sK0)
        | sK1 = X3 )
    | ~ spl4_3 ),
    inference(superposition,[],[f75,f88])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f58,f45])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f572,plain,
    ( ~ r2_hidden(sK3(sK1,sK0),sK1)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f566,f340])).

fof(f566,plain,
    ( sK0 = sK1
    | ~ r2_hidden(sK3(sK1,sK0),sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f540,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | X0 = X1
      | ~ r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f604,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_26 ),
    inference(avatar_contradiction_clause,[],[f603])).

fof(f603,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f597,f398])).

fof(f398,plain,
    ( r2_hidden(sK1,sK1)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f394,f94])).

fof(f94,plain,
    ( v3_ordinal1(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f394,plain,
    ( r2_hidden(sK1,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f389,f347])).

fof(f347,plain,
    ( ! [X0] :
        ( ~ r1_ordinal1(sK0,X0)
        | r2_hidden(sK1,X0)
        | ~ v3_ordinal1(X0) )
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f342,f94])).

fof(f342,plain,
    ( ! [X0] :
        ( ~ r1_ordinal1(sK0,X0)
        | r2_hidden(sK1,X0)
        | ~ v3_ordinal1(X0)
        | ~ v3_ordinal1(sK1) )
    | ~ spl4_3 ),
    inference(superposition,[],[f69,f88])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f52,f45])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f389,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f384,f37])).

fof(f37,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ( v4_ordinal1(sK0)
        & sK0 = k1_ordinal1(sK1)
        & v3_ordinal1(sK1) )
      | ( ! [X2] :
            ( k1_ordinal1(X2) != sK0
            | ~ v3_ordinal1(X2) )
        & ~ v4_ordinal1(sK0) ) )
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f24,f23])).

fof(f23,plain,
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

fof(f24,plain,
    ( ? [X1] :
        ( k1_ordinal1(X1) = sK0
        & v3_ordinal1(X1) )
   => ( sK0 = k1_ordinal1(sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_ordinal1)).

fof(f384,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f348,f358])).

fof(f358,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f357,f88])).

fof(f357,plain,
    ( r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f356,f37])).

fof(f356,plain,
    ( r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | ~ v3_ordinal1(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f355,f83])).

fof(f83,plain,
    ( v4_ordinal1(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_2
  <=> v4_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f355,plain,
    ( r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | ~ v4_ordinal1(sK0)
    | ~ v3_ordinal1(sK0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f351,f94])).

fof(f351,plain,
    ( r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)
    | ~ v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0)
    | ~ v3_ordinal1(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f346,f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X0)
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f47,f45])).

fof(f47,plain,(
    ! [X2,X0] :
      ( r2_hidden(k1_ordinal1(X2),X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
        & r2_hidden(sK2(X0),X0)
        & v3_ordinal1(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).

fof(f346,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_3 ),
    inference(superposition,[],[f76,f88])).

fof(f76,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f60,f45])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f348,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | r1_ordinal1(X1,sK1)
        | ~ v3_ordinal1(X1) )
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f343,f94])).

fof(f343,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | r1_ordinal1(X1,sK1)
        | ~ v3_ordinal1(sK1)
        | ~ v3_ordinal1(X1) )
    | ~ spl4_3 ),
    inference(superposition,[],[f72,f88])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f53,f45])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f597,plain,
    ( ~ r2_hidden(sK1,sK1)
    | ~ spl4_3
    | ~ spl4_26 ),
    inference(backward_demodulation,[],[f572,f580])).

fof(f580,plain,
    ( sK1 = sK3(sK1,sK0)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f578])).

fof(f329,plain,
    ( ~ spl4_1
    | spl4_2
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | ~ spl4_1
    | spl4_2
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f325,f229])).

fof(f229,plain,
    ( v3_ordinal1(sK2(sK0))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f227,f37])).

fof(f227,plain,
    ( v3_ordinal1(sK2(sK0))
    | ~ v3_ordinal1(sK0)
    | spl4_2 ),
    inference(resolution,[],[f82,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | v3_ordinal1(sK2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,
    ( ~ v4_ordinal1(sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f325,plain,
    ( ~ v3_ordinal1(sK2(sK0))
    | ~ spl4_1
    | ~ spl4_15 ),
    inference(trivial_inequality_removal,[],[f324])).

fof(f324,plain,
    ( sK0 != sK0
    | ~ v3_ordinal1(sK2(sK0))
    | ~ spl4_1
    | ~ spl4_15 ),
    inference(superposition,[],[f79,f271])).

fof(f271,plain,
    ( sK0 = k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl4_15
  <=> sK0 = k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f79,plain,
    ( ! [X2] :
        ( sK0 != k2_xboole_0(X2,k1_tarski(X2))
        | ~ v3_ordinal1(X2) )
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_1
  <=> ! [X2] :
        ( sK0 != k2_xboole_0(X2,k1_tarski(X2))
        | ~ v3_ordinal1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f303,plain,
    ( spl4_2
    | ~ spl4_16 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | spl4_2
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f301,f37])).

fof(f301,plain,
    ( ~ v3_ordinal1(sK0)
    | spl4_2
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f297,f82])).

fof(f297,plain,
    ( v4_ordinal1(sK0)
    | ~ v3_ordinal1(sK0)
    | ~ spl4_16 ),
    inference(resolution,[],[f275,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r2_hidden(k2_xboole_0(sK2(X0),k1_tarski(sK2(X0))),X0)
      | v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f50,f45])).

fof(f50,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f275,plain,
    ( r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl4_16
  <=> r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f276,plain,
    ( spl4_15
    | spl4_16
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f263,f244,f273,f269])).

fof(f244,plain,
    ( spl4_12
  <=> r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),k2_xboole_0(sK0,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f263,plain,
    ( r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0)
    | sK0 = k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))
    | ~ spl4_12 ),
    inference(resolution,[],[f246,f75])).

fof(f246,plain,
    ( r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f244])).

fof(f250,plain,
    ( spl4_2
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | spl4_2
    | spl4_11 ),
    inference(subsumption_resolution,[],[f248,f229])).

fof(f248,plain,
    ( ~ v3_ordinal1(sK2(sK0))
    | spl4_11 ),
    inference(resolution,[],[f242,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f46,f45])).

fof(f46,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v3_ordinal1(k1_ordinal1(X0))
        & ~ v1_xboole_0(k1_ordinal1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_ordinal1)).

fof(f242,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl4_11
  <=> v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f247,plain,
    ( ~ spl4_11
    | spl4_12
    | spl4_2 ),
    inference(avatar_split_clause,[],[f238,f81,f244,f240])).

fof(f238,plain,
    ( r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f237,f37])).

fof(f237,plain,
    ( r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))))
    | spl4_2 ),
    inference(resolution,[],[f235,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f54,f45])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f235,plain,
    ( r1_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f234,f229])).

fof(f234,plain,
    ( r1_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0)
    | ~ v3_ordinal1(sK2(sK0))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f232,f37])).

fof(f232,plain,
    ( r1_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK2(sK0))
    | spl4_2 ),
    inference(resolution,[],[f230,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f51,f45])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f230,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f228,f37])).

fof(f228,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ v3_ordinal1(sK0)
    | spl4_2 ),
    inference(resolution,[],[f82,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | r2_hidden(sK2(X0),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f96,plain,
    ( ~ spl4_2
    | spl4_4 ),
    inference(avatar_split_clause,[],[f38,f92,f81])).

fof(f38,plain,
    ( v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f90,plain,
    ( ~ spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f63,f86,f81])).

fof(f63,plain,
    ( sK0 = k2_xboole_0(sK1,k1_tarski(sK1))
    | ~ v4_ordinal1(sK0) ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f40,plain,
    ( sK0 = k1_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f89,plain,
    ( spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f62,f86,f78])).

fof(f62,plain,(
    ! [X2] :
      ( sK0 = k2_xboole_0(sK1,k1_tarski(sK1))
      | sK0 != k2_xboole_0(X2,k1_tarski(X2))
      | ~ v3_ordinal1(X2) ) ),
    inference(definition_unfolding,[],[f41,f45,f45])).

fof(f41,plain,(
    ! [X2] :
      ( sK0 = k1_ordinal1(sK1)
      | k1_ordinal1(X2) != sK0
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f84,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f61,f81,f78])).

fof(f61,plain,(
    ! [X2] :
      ( v4_ordinal1(sK0)
      | sK0 != k2_xboole_0(X2,k1_tarski(X2))
      | ~ v3_ordinal1(X2) ) ),
    inference(definition_unfolding,[],[f43,f45])).

fof(f43,plain,(
    ! [X2] :
      ( v4_ordinal1(sK0)
      | k1_ordinal1(X2) != sK0
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:22:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (19082)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (19078)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (19103)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (19099)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (19078)Refutation not found, incomplete strategy% (19078)------------------------------
% 0.21/0.51  % (19078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19080)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (19090)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (19095)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (19079)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (19077)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (19078)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19078)Memory used [KB]: 10746
% 0.21/0.52  % (19078)Time elapsed: 0.095 s
% 0.21/0.52  % (19078)------------------------------
% 0.21/0.52  % (19078)------------------------------
% 0.21/0.52  % (19081)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (19099)Refutation not found, incomplete strategy% (19099)------------------------------
% 0.21/0.52  % (19099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19091)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (19099)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19099)Memory used [KB]: 10746
% 0.21/0.52  % (19099)Time elapsed: 0.108 s
% 0.21/0.52  % (19099)------------------------------
% 0.21/0.52  % (19099)------------------------------
% 0.21/0.53  % (19086)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (19097)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (19102)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (19089)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (19101)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (19087)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (19083)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (19107)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (19076)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (19094)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (19100)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (19088)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (19104)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (19093)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (19096)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (19106)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (19085)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (19098)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (19084)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (19084)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 1.62/0.58  % SZS output start Proof for theBenchmark
% 1.62/0.58  fof(f643,plain,(
% 1.62/0.58    $false),
% 1.62/0.58    inference(avatar_sat_refutation,[],[f84,f89,f90,f96,f247,f250,f276,f303,f329,f604,f642])).
% 1.62/0.58  fof(f642,plain,(
% 1.62/0.58    ~spl4_3 | spl4_26),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f641])).
% 1.62/0.58  fof(f641,plain,(
% 1.62/0.58    $false | (~spl4_3 | spl4_26)),
% 1.62/0.58    inference(subsumption_resolution,[],[f640,f579])).
% 1.62/0.58  fof(f579,plain,(
% 1.62/0.58    sK1 != sK3(sK1,sK0) | spl4_26),
% 1.62/0.58    inference(avatar_component_clause,[],[f578])).
% 1.62/0.58  fof(f578,plain,(
% 1.62/0.58    spl4_26 <=> sK1 = sK3(sK1,sK0)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.62/0.58  fof(f640,plain,(
% 1.62/0.58    sK1 = sK3(sK1,sK0) | ~spl4_3),
% 1.62/0.58    inference(subsumption_resolution,[],[f639,f540])).
% 1.62/0.58  fof(f540,plain,(
% 1.62/0.58    r2_hidden(sK3(sK1,sK0),sK0) | ~spl4_3),
% 1.62/0.58    inference(subsumption_resolution,[],[f528,f340])).
% 1.62/0.58  fof(f340,plain,(
% 1.62/0.58    sK0 != sK1 | ~spl4_3),
% 1.62/0.58    inference(superposition,[],[f65,f88])).
% 1.62/0.58  fof(f88,plain,(
% 1.62/0.58    sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) | ~spl4_3),
% 1.62/0.58    inference(avatar_component_clause,[],[f86])).
% 1.62/0.58  fof(f86,plain,(
% 1.62/0.58    spl4_3 <=> sK0 = k2_xboole_0(sK1,k1_tarski(sK1))),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.62/0.58  fof(f65,plain,(
% 1.62/0.58    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) != X0) )),
% 1.62/0.58    inference(definition_unfolding,[],[f44,f45])).
% 1.62/0.58  fof(f45,plain,(
% 1.62/0.58    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f2])).
% 1.62/0.58  fof(f2,axiom,(
% 1.62/0.58    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.62/0.58  fof(f44,plain,(
% 1.62/0.58    ( ! [X0] : (k1_ordinal1(X0) != X0) )),
% 1.62/0.58    inference(cnf_transformation,[],[f5])).
% 1.62/0.58  fof(f5,axiom,(
% 1.62/0.58    ! [X0] : k1_ordinal1(X0) != X0),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).
% 1.62/0.58  fof(f528,plain,(
% 1.62/0.58    r2_hidden(sK3(sK1,sK0),sK0) | sK0 = sK1 | ~spl4_3),
% 1.62/0.58    inference(factoring,[],[f360])).
% 1.62/0.58  fof(f360,plain,(
% 1.62/0.58    ( ! [X1] : (r2_hidden(sK3(sK1,X1),sK0) | r2_hidden(sK3(sK1,X1),X1) | sK1 = X1) ) | ~spl4_3),
% 1.62/0.58    inference(resolution,[],[f344,f56])).
% 1.62/0.58  fof(f56,plain,(
% 1.62/0.58    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0) | X0 = X1) )),
% 1.62/0.58    inference(cnf_transformation,[],[f34])).
% 1.62/0.58  fof(f34,plain,(
% 1.62/0.58    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 1.62/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 1.62/0.58  fof(f33,plain,(
% 1.62/0.58    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 1.62/0.58    introduced(choice_axiom,[])).
% 1.62/0.58  fof(f32,plain,(
% 1.62/0.58    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.62/0.58    inference(nnf_transformation,[],[f22])).
% 1.62/0.58  fof(f22,plain,(
% 1.62/0.58    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.62/0.58    inference(ennf_transformation,[],[f1])).
% 1.62/0.58  fof(f1,axiom,(
% 1.62/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.62/0.58  fof(f344,plain,(
% 1.62/0.58    ( ! [X2] : (~r2_hidden(X2,sK1) | r2_hidden(X2,sK0)) ) | ~spl4_3),
% 1.62/0.58    inference(superposition,[],[f74,f88])).
% 1.62/0.58  fof(f74,plain,(
% 1.62/0.58    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 1.62/0.58    inference(definition_unfolding,[],[f59,f45])).
% 1.62/0.58  fof(f59,plain,(
% 1.62/0.58    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f36])).
% 1.62/0.58  fof(f36,plain,(
% 1.62/0.58    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 1.62/0.58    inference(flattening,[],[f35])).
% 1.62/0.58  fof(f35,plain,(
% 1.62/0.58    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 1.62/0.58    inference(nnf_transformation,[],[f4])).
% 1.62/0.58  fof(f4,axiom,(
% 1.62/0.58    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 1.62/0.58  fof(f639,plain,(
% 1.62/0.58    ~r2_hidden(sK3(sK1,sK0),sK0) | sK1 = sK3(sK1,sK0) | ~spl4_3),
% 1.62/0.58    inference(resolution,[],[f572,f345])).
% 1.62/0.58  fof(f345,plain,(
% 1.62/0.58    ( ! [X3] : (r2_hidden(X3,sK1) | ~r2_hidden(X3,sK0) | sK1 = X3) ) | ~spl4_3),
% 1.62/0.58    inference(superposition,[],[f75,f88])).
% 1.62/0.58  fof(f75,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | r2_hidden(X0,X1) | X0 = X1) )),
% 1.62/0.58    inference(definition_unfolding,[],[f58,f45])).
% 1.62/0.58  fof(f58,plain,(
% 1.62/0.58    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f36])).
% 1.62/0.58  fof(f572,plain,(
% 1.62/0.58    ~r2_hidden(sK3(sK1,sK0),sK1) | ~spl4_3),
% 1.62/0.58    inference(subsumption_resolution,[],[f566,f340])).
% 1.62/0.58  fof(f566,plain,(
% 1.62/0.58    sK0 = sK1 | ~r2_hidden(sK3(sK1,sK0),sK1) | ~spl4_3),
% 1.62/0.58    inference(resolution,[],[f540,f57])).
% 1.62/0.58  fof(f57,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | X0 = X1 | ~r2_hidden(sK3(X0,X1),X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f34])).
% 1.62/0.58  fof(f604,plain,(
% 1.62/0.58    ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_26),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f603])).
% 1.62/0.58  fof(f603,plain,(
% 1.62/0.58    $false | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_26)),
% 1.62/0.58    inference(subsumption_resolution,[],[f597,f398])).
% 1.62/0.58  fof(f398,plain,(
% 1.62/0.58    r2_hidden(sK1,sK1) | (~spl4_2 | ~spl4_3 | ~spl4_4)),
% 1.62/0.58    inference(subsumption_resolution,[],[f394,f94])).
% 1.62/0.58  fof(f94,plain,(
% 1.62/0.58    v3_ordinal1(sK1) | ~spl4_4),
% 1.62/0.58    inference(avatar_component_clause,[],[f92])).
% 1.62/0.58  fof(f92,plain,(
% 1.62/0.58    spl4_4 <=> v3_ordinal1(sK1)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.62/0.58  fof(f394,plain,(
% 1.62/0.58    r2_hidden(sK1,sK1) | ~v3_ordinal1(sK1) | (~spl4_2 | ~spl4_3 | ~spl4_4)),
% 1.62/0.58    inference(resolution,[],[f389,f347])).
% 1.62/0.58  fof(f347,plain,(
% 1.62/0.58    ( ! [X0] : (~r1_ordinal1(sK0,X0) | r2_hidden(sK1,X0) | ~v3_ordinal1(X0)) ) | (~spl4_3 | ~spl4_4)),
% 1.62/0.58    inference(subsumption_resolution,[],[f342,f94])).
% 1.62/0.58  fof(f342,plain,(
% 1.62/0.58    ( ! [X0] : (~r1_ordinal1(sK0,X0) | r2_hidden(sK1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(sK1)) ) | ~spl4_3),
% 1.62/0.58    inference(superposition,[],[f69,f88])).
% 1.62/0.58  fof(f69,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.62/0.58    inference(definition_unfolding,[],[f52,f45])).
% 1.62/0.58  fof(f52,plain,(
% 1.62/0.58    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f30])).
% 1.62/0.58  fof(f30,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : (((r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.62/0.58    inference(nnf_transformation,[],[f18])).
% 1.62/0.58  fof(f18,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f7])).
% 1.62/0.58  fof(f7,axiom,(
% 1.62/0.58    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 1.62/0.58  fof(f389,plain,(
% 1.62/0.58    r1_ordinal1(sK0,sK1) | (~spl4_2 | ~spl4_3 | ~spl4_4)),
% 1.62/0.58    inference(subsumption_resolution,[],[f384,f37])).
% 1.62/0.58  fof(f37,plain,(
% 1.62/0.58    v3_ordinal1(sK0)),
% 1.62/0.58    inference(cnf_transformation,[],[f25])).
% 1.62/0.58  fof(f25,plain,(
% 1.62/0.58    ((v4_ordinal1(sK0) & (sK0 = k1_ordinal1(sK1) & v3_ordinal1(sK1))) | (! [X2] : (k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK0))) & v3_ordinal1(sK0)),
% 1.62/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f24,f23])).
% 1.62/0.58  fof(f23,plain,(
% 1.62/0.58    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0)) => (((v4_ordinal1(sK0) & ? [X1] : (k1_ordinal1(X1) = sK0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK0))) & v3_ordinal1(sK0))),
% 1.62/0.58    introduced(choice_axiom,[])).
% 1.62/0.58  fof(f24,plain,(
% 1.62/0.58    ? [X1] : (k1_ordinal1(X1) = sK0 & v3_ordinal1(X1)) => (sK0 = k1_ordinal1(sK1) & v3_ordinal1(sK1))),
% 1.62/0.58    introduced(choice_axiom,[])).
% 1.62/0.58  fof(f14,plain,(
% 1.62/0.58    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f12])).
% 1.62/0.58  fof(f12,plain,(
% 1.62/0.58    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X2] : (v3_ordinal1(X2) => k1_ordinal1(X2) != X0) & ~v4_ordinal1(X0))))),
% 1.62/0.58    inference(rectify,[],[f11])).
% 1.62/0.58  fof(f11,negated_conjecture,(
% 1.62/0.58    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 1.62/0.58    inference(negated_conjecture,[],[f10])).
% 1.62/0.58  fof(f10,conjecture,(
% 1.62/0.58    ! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_ordinal1)).
% 1.62/0.58  fof(f384,plain,(
% 1.62/0.58    r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_4)),
% 1.62/0.58    inference(resolution,[],[f348,f358])).
% 1.62/0.58  fof(f358,plain,(
% 1.62/0.58    r2_hidden(sK0,sK0) | (~spl4_2 | ~spl4_3 | ~spl4_4)),
% 1.62/0.58    inference(forward_demodulation,[],[f357,f88])).
% 1.62/0.58  fof(f357,plain,(
% 1.62/0.58    r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | (~spl4_2 | ~spl4_3 | ~spl4_4)),
% 1.62/0.58    inference(subsumption_resolution,[],[f356,f37])).
% 1.62/0.58  fof(f356,plain,(
% 1.62/0.58    r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | ~v3_ordinal1(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_4)),
% 1.62/0.58    inference(subsumption_resolution,[],[f355,f83])).
% 1.62/0.58  fof(f83,plain,(
% 1.62/0.58    v4_ordinal1(sK0) | ~spl4_2),
% 1.62/0.58    inference(avatar_component_clause,[],[f81])).
% 1.62/0.58  fof(f81,plain,(
% 1.62/0.58    spl4_2 <=> v4_ordinal1(sK0)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.62/0.58  fof(f355,plain,(
% 1.62/0.58    r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | ~v4_ordinal1(sK0) | ~v3_ordinal1(sK0) | (~spl4_3 | ~spl4_4)),
% 1.62/0.58    inference(subsumption_resolution,[],[f351,f94])).
% 1.62/0.58  fof(f351,plain,(
% 1.62/0.58    r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) | ~v3_ordinal1(sK1) | ~v4_ordinal1(sK0) | ~v3_ordinal1(sK0) | ~spl4_3),
% 1.62/0.58    inference(resolution,[],[f346,f68])).
% 1.62/0.58  fof(f68,plain,(
% 1.62/0.58    ( ! [X2,X0] : (~r2_hidden(X2,X0) | r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X0) | ~v3_ordinal1(X2) | ~v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 1.62/0.58    inference(definition_unfolding,[],[f47,f45])).
% 1.62/0.58  fof(f47,plain,(
% 1.62/0.58    ( ! [X2,X0] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | ~v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f29])).
% 1.62/0.58  fof(f29,plain,(
% 1.62/0.58    ! [X0] : (((v4_ordinal1(X0) | (~r2_hidden(k1_ordinal1(sK2(X0)),X0) & r2_hidden(sK2(X0),X0) & v3_ordinal1(sK2(X0)))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 1.62/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 1.62/0.58  fof(f28,plain,(
% 1.62/0.58    ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK2(X0)),X0) & r2_hidden(sK2(X0),X0) & v3_ordinal1(sK2(X0))))),
% 1.62/0.58    introduced(choice_axiom,[])).
% 1.62/0.58  fof(f27,plain,(
% 1.62/0.58    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 1.62/0.58    inference(rectify,[],[f26])).
% 1.62/0.58  fof(f26,plain,(
% 1.62/0.58    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 1.62/0.58    inference(nnf_transformation,[],[f17])).
% 1.62/0.58  fof(f17,plain,(
% 1.62/0.58    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 1.62/0.58    inference(flattening,[],[f16])).
% 1.62/0.58  fof(f16,plain,(
% 1.62/0.58    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f9])).
% 1.62/0.58  fof(f9,axiom,(
% 1.62/0.58    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).
% 1.62/0.58  fof(f346,plain,(
% 1.62/0.58    r2_hidden(sK1,sK0) | ~spl4_3),
% 1.62/0.58    inference(superposition,[],[f76,f88])).
% 1.62/0.58  fof(f76,plain,(
% 1.62/0.58    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 1.62/0.58    inference(equality_resolution,[],[f73])).
% 1.62/0.58  fof(f73,plain,(
% 1.62/0.58    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 != X1) )),
% 1.62/0.58    inference(definition_unfolding,[],[f60,f45])).
% 1.62/0.58  fof(f60,plain,(
% 1.62/0.58    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 1.62/0.58    inference(cnf_transformation,[],[f36])).
% 1.62/0.58  fof(f348,plain,(
% 1.62/0.58    ( ! [X1] : (~r2_hidden(X1,sK0) | r1_ordinal1(X1,sK1) | ~v3_ordinal1(X1)) ) | (~spl4_3 | ~spl4_4)),
% 1.62/0.58    inference(subsumption_resolution,[],[f343,f94])).
% 1.62/0.58  fof(f343,plain,(
% 1.62/0.58    ( ! [X1] : (~r2_hidden(X1,sK0) | r1_ordinal1(X1,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(X1)) ) | ~spl4_3),
% 1.62/0.58    inference(superposition,[],[f72,f88])).
% 1.62/0.58  fof(f72,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.62/0.58    inference(definition_unfolding,[],[f53,f45])).
% 1.62/0.58  fof(f53,plain,(
% 1.62/0.58    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f31])).
% 1.62/0.58  fof(f31,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.62/0.58    inference(nnf_transformation,[],[f19])).
% 1.62/0.58  fof(f19,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f8])).
% 1.62/0.58  fof(f8,axiom,(
% 1.62/0.58    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).
% 1.62/0.58  fof(f597,plain,(
% 1.62/0.58    ~r2_hidden(sK1,sK1) | (~spl4_3 | ~spl4_26)),
% 1.62/0.58    inference(backward_demodulation,[],[f572,f580])).
% 1.62/0.58  fof(f580,plain,(
% 1.62/0.58    sK1 = sK3(sK1,sK0) | ~spl4_26),
% 1.62/0.58    inference(avatar_component_clause,[],[f578])).
% 1.62/0.58  fof(f329,plain,(
% 1.62/0.58    ~spl4_1 | spl4_2 | ~spl4_15),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f328])).
% 1.62/0.58  fof(f328,plain,(
% 1.62/0.58    $false | (~spl4_1 | spl4_2 | ~spl4_15)),
% 1.62/0.58    inference(subsumption_resolution,[],[f325,f229])).
% 1.62/0.58  fof(f229,plain,(
% 1.62/0.58    v3_ordinal1(sK2(sK0)) | spl4_2),
% 1.62/0.58    inference(subsumption_resolution,[],[f227,f37])).
% 1.62/0.58  fof(f227,plain,(
% 1.62/0.58    v3_ordinal1(sK2(sK0)) | ~v3_ordinal1(sK0) | spl4_2),
% 1.62/0.58    inference(resolution,[],[f82,f48])).
% 1.62/0.58  fof(f48,plain,(
% 1.62/0.58    ( ! [X0] : (v4_ordinal1(X0) | v3_ordinal1(sK2(X0)) | ~v3_ordinal1(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f29])).
% 1.62/0.58  fof(f82,plain,(
% 1.62/0.58    ~v4_ordinal1(sK0) | spl4_2),
% 1.62/0.58    inference(avatar_component_clause,[],[f81])).
% 1.62/0.58  fof(f325,plain,(
% 1.62/0.58    ~v3_ordinal1(sK2(sK0)) | (~spl4_1 | ~spl4_15)),
% 1.62/0.58    inference(trivial_inequality_removal,[],[f324])).
% 1.62/0.58  fof(f324,plain,(
% 1.62/0.58    sK0 != sK0 | ~v3_ordinal1(sK2(sK0)) | (~spl4_1 | ~spl4_15)),
% 1.62/0.58    inference(superposition,[],[f79,f271])).
% 1.62/0.58  fof(f271,plain,(
% 1.62/0.58    sK0 = k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))) | ~spl4_15),
% 1.62/0.58    inference(avatar_component_clause,[],[f269])).
% 1.62/0.58  fof(f269,plain,(
% 1.62/0.58    spl4_15 <=> sK0 = k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.62/0.58  fof(f79,plain,(
% 1.62/0.58    ( ! [X2] : (sK0 != k2_xboole_0(X2,k1_tarski(X2)) | ~v3_ordinal1(X2)) ) | ~spl4_1),
% 1.62/0.58    inference(avatar_component_clause,[],[f78])).
% 1.62/0.58  fof(f78,plain,(
% 1.62/0.58    spl4_1 <=> ! [X2] : (sK0 != k2_xboole_0(X2,k1_tarski(X2)) | ~v3_ordinal1(X2))),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.62/0.58  fof(f303,plain,(
% 1.62/0.58    spl4_2 | ~spl4_16),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f302])).
% 1.62/0.58  fof(f302,plain,(
% 1.62/0.58    $false | (spl4_2 | ~spl4_16)),
% 1.62/0.58    inference(subsumption_resolution,[],[f301,f37])).
% 1.62/0.58  fof(f301,plain,(
% 1.62/0.58    ~v3_ordinal1(sK0) | (spl4_2 | ~spl4_16)),
% 1.62/0.58    inference(subsumption_resolution,[],[f297,f82])).
% 1.62/0.58  fof(f297,plain,(
% 1.62/0.58    v4_ordinal1(sK0) | ~v3_ordinal1(sK0) | ~spl4_16),
% 1.62/0.58    inference(resolution,[],[f275,f67])).
% 1.62/0.58  fof(f67,plain,(
% 1.62/0.58    ( ! [X0] : (~r2_hidden(k2_xboole_0(sK2(X0),k1_tarski(sK2(X0))),X0) | v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 1.62/0.58    inference(definition_unfolding,[],[f50,f45])).
% 1.62/0.58  fof(f50,plain,(
% 1.62/0.58    ( ! [X0] : (v4_ordinal1(X0) | ~r2_hidden(k1_ordinal1(sK2(X0)),X0) | ~v3_ordinal1(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f29])).
% 1.62/0.58  fof(f275,plain,(
% 1.62/0.58    r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0) | ~spl4_16),
% 1.62/0.58    inference(avatar_component_clause,[],[f273])).
% 1.62/0.58  fof(f273,plain,(
% 1.62/0.58    spl4_16 <=> r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.62/0.58  fof(f276,plain,(
% 1.62/0.58    spl4_15 | spl4_16 | ~spl4_12),
% 1.62/0.58    inference(avatar_split_clause,[],[f263,f244,f273,f269])).
% 1.62/0.58  fof(f244,plain,(
% 1.62/0.58    spl4_12 <=> r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),k2_xboole_0(sK0,k1_tarski(sK0)))),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.62/0.58  fof(f263,plain,(
% 1.62/0.58    r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0) | sK0 = k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))) | ~spl4_12),
% 1.62/0.58    inference(resolution,[],[f246,f75])).
% 1.62/0.58  fof(f246,plain,(
% 1.62/0.58    r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),k2_xboole_0(sK0,k1_tarski(sK0))) | ~spl4_12),
% 1.62/0.58    inference(avatar_component_clause,[],[f244])).
% 1.62/0.58  fof(f250,plain,(
% 1.62/0.58    spl4_2 | spl4_11),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f249])).
% 1.62/0.58  fof(f249,plain,(
% 1.62/0.58    $false | (spl4_2 | spl4_11)),
% 1.62/0.58    inference(subsumption_resolution,[],[f248,f229])).
% 1.62/0.58  fof(f248,plain,(
% 1.62/0.58    ~v3_ordinal1(sK2(sK0)) | spl4_11),
% 1.62/0.58    inference(resolution,[],[f242,f66])).
% 1.62/0.58  fof(f66,plain,(
% 1.62/0.58    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 1.62/0.58    inference(definition_unfolding,[],[f46,f45])).
% 1.62/0.58  fof(f46,plain,(
% 1.62/0.58    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f15])).
% 1.62/0.58  fof(f15,plain,(
% 1.62/0.58    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f13])).
% 1.62/0.58  fof(f13,plain,(
% 1.62/0.58    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 1.62/0.58    inference(pure_predicate_removal,[],[f3])).
% 1.62/0.58  fof(f3,axiom,(
% 1.62/0.58    ! [X0] : (v3_ordinal1(X0) => (v3_ordinal1(k1_ordinal1(X0)) & ~v1_xboole_0(k1_ordinal1(X0))))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_ordinal1)).
% 1.62/0.58  fof(f242,plain,(
% 1.62/0.58    ~v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))) | spl4_11),
% 1.62/0.58    inference(avatar_component_clause,[],[f240])).
% 1.62/0.58  fof(f240,plain,(
% 1.62/0.58    spl4_11 <=> v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))))),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.62/0.58  fof(f247,plain,(
% 1.62/0.58    ~spl4_11 | spl4_12 | spl4_2),
% 1.62/0.58    inference(avatar_split_clause,[],[f238,f81,f244,f240])).
% 1.62/0.58  fof(f238,plain,(
% 1.62/0.58    r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),k2_xboole_0(sK0,k1_tarski(sK0))) | ~v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))) | spl4_2),
% 1.62/0.58    inference(subsumption_resolution,[],[f237,f37])).
% 1.62/0.58  fof(f237,plain,(
% 1.62/0.58    r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),k2_xboole_0(sK0,k1_tarski(sK0))) | ~v3_ordinal1(sK0) | ~v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))) | spl4_2),
% 1.62/0.58    inference(resolution,[],[f235,f71])).
% 1.62/0.58  fof(f71,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.62/0.58    inference(definition_unfolding,[],[f54,f45])).
% 1.62/0.58  fof(f54,plain,(
% 1.62/0.58    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f31])).
% 1.62/0.58  fof(f235,plain,(
% 1.62/0.58    r1_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0) | spl4_2),
% 1.62/0.58    inference(subsumption_resolution,[],[f234,f229])).
% 1.62/0.58  fof(f234,plain,(
% 1.62/0.58    r1_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0) | ~v3_ordinal1(sK2(sK0)) | spl4_2),
% 1.62/0.58    inference(subsumption_resolution,[],[f232,f37])).
% 1.62/0.58  fof(f232,plain,(
% 1.62/0.58    r1_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK2(sK0)) | spl4_2),
% 1.62/0.58    inference(resolution,[],[f230,f70])).
% 1.62/0.58  fof(f70,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.62/0.58    inference(definition_unfolding,[],[f51,f45])).
% 1.62/0.58  fof(f51,plain,(
% 1.62/0.58    ( ! [X0,X1] : (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f30])).
% 1.62/0.58  fof(f230,plain,(
% 1.62/0.58    r2_hidden(sK2(sK0),sK0) | spl4_2),
% 1.62/0.58    inference(subsumption_resolution,[],[f228,f37])).
% 1.62/0.58  fof(f228,plain,(
% 1.62/0.58    r2_hidden(sK2(sK0),sK0) | ~v3_ordinal1(sK0) | spl4_2),
% 1.62/0.58    inference(resolution,[],[f82,f49])).
% 1.62/0.58  fof(f49,plain,(
% 1.62/0.58    ( ! [X0] : (v4_ordinal1(X0) | r2_hidden(sK2(X0),X0) | ~v3_ordinal1(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f29])).
% 1.62/0.58  fof(f96,plain,(
% 1.62/0.58    ~spl4_2 | spl4_4),
% 1.62/0.58    inference(avatar_split_clause,[],[f38,f92,f81])).
% 1.62/0.58  fof(f38,plain,(
% 1.62/0.58    v3_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 1.62/0.58    inference(cnf_transformation,[],[f25])).
% 1.62/0.58  fof(f90,plain,(
% 1.62/0.58    ~spl4_2 | spl4_3),
% 1.62/0.58    inference(avatar_split_clause,[],[f63,f86,f81])).
% 1.62/0.58  fof(f63,plain,(
% 1.62/0.58    sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) | ~v4_ordinal1(sK0)),
% 1.62/0.58    inference(definition_unfolding,[],[f40,f45])).
% 1.62/0.58  fof(f40,plain,(
% 1.62/0.58    sK0 = k1_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 1.62/0.58    inference(cnf_transformation,[],[f25])).
% 1.62/0.58  fof(f89,plain,(
% 1.62/0.58    spl4_1 | spl4_3),
% 1.62/0.58    inference(avatar_split_clause,[],[f62,f86,f78])).
% 1.62/0.58  fof(f62,plain,(
% 1.62/0.58    ( ! [X2] : (sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) | sK0 != k2_xboole_0(X2,k1_tarski(X2)) | ~v3_ordinal1(X2)) )),
% 1.62/0.58    inference(definition_unfolding,[],[f41,f45,f45])).
% 1.62/0.58  fof(f41,plain,(
% 1.62/0.58    ( ! [X2] : (sK0 = k1_ordinal1(sK1) | k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f25])).
% 1.62/0.58  fof(f84,plain,(
% 1.62/0.58    spl4_1 | spl4_2),
% 1.62/0.58    inference(avatar_split_clause,[],[f61,f81,f78])).
% 1.62/0.58  fof(f61,plain,(
% 1.62/0.58    ( ! [X2] : (v4_ordinal1(sK0) | sK0 != k2_xboole_0(X2,k1_tarski(X2)) | ~v3_ordinal1(X2)) )),
% 1.62/0.58    inference(definition_unfolding,[],[f43,f45])).
% 1.62/0.58  fof(f43,plain,(
% 1.62/0.58    ( ! [X2] : (v4_ordinal1(sK0) | k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f25])).
% 1.62/0.58  % SZS output end Proof for theBenchmark
% 1.62/0.58  % (19084)------------------------------
% 1.62/0.58  % (19084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.58  % (19084)Termination reason: Refutation
% 1.62/0.58  
% 1.62/0.58  % (19084)Memory used [KB]: 10874
% 1.62/0.58  % (19084)Time elapsed: 0.149 s
% 1.62/0.58  % (19084)------------------------------
% 1.62/0.58  % (19084)------------------------------
% 1.62/0.59  % (19071)Success in time 0.221 s
%------------------------------------------------------------------------------
