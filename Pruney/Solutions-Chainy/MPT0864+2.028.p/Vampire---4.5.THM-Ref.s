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
% DateTime   : Thu Dec  3 12:58:34 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 159 expanded)
%              Number of leaves         :   24 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  244 ( 483 expanded)
%              Number of equality atoms :  136 ( 271 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f167,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f72,f80,f85,f91,f121,f127,f132,f144,f165])).

fof(f165,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f116,f154])).

fof(f154,plain,(
    ! [X1] : k1_xboole_0 != k2_tarski(X1,X1) ),
    inference(forward_demodulation,[],[f58,f96])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f51,f54])).

fof(f54,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f46,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f51,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f40,f44,f45])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f58,plain,(
    ! [X1] : k2_tarski(X1,X1) != k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1))) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_tarski(X0,X0) != k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) ) ),
    inference(definition_unfolding,[],[f41,f43,f44,f43,f43])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f116,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl5_7
  <=> k1_xboole_0 = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f144,plain,
    ( k1_mcart_1(sK0) != sK1
    | sK0 != k1_mcart_1(sK0)
    | r2_hidden(sK1,k2_tarski(sK0,sK0))
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f132,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl5_9 ),
    inference(unit_resulting_resolution,[],[f56,f126])).

fof(f126,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl5_9
  <=> r2_hidden(sK0,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f56,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f37,f43])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f127,plain,
    ( spl5_7
    | ~ spl5_9
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f122,f88,f124,f114])).

fof(f88,plain,
    ( spl5_6
  <=> sK0 = k4_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f122,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | k1_xboole_0 = k2_tarski(sK0,sK0)
    | ~ spl5_6 ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK0,k2_tarski(X0,X0))
        | k1_xboole_0 = k2_tarski(X0,X0) )
    | ~ spl5_6 ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK0,k2_tarski(X0,X0))
        | k1_xboole_0 = k2_tarski(X0,X0)
        | k1_xboole_0 = k2_tarski(X0,X0) )
    | ~ spl5_6 ),
    inference(superposition,[],[f106,f95])).

fof(f95,plain,(
    ! [X1] :
      ( sK3(k2_tarski(X1,X1)) = X1
      | k1_xboole_0 = k2_tarski(X1,X1) ) ),
    inference(resolution,[],[f57,f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f57,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f36,f43])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f106,plain,
    ( ! [X1] :
        ( sK0 != sK3(X1)
        | ~ r2_hidden(sK0,X1)
        | k1_xboole_0 = X1 )
    | ~ spl5_6 ),
    inference(superposition,[],[f35,f90])).

fof(f90,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f35,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK3(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f121,plain,
    ( spl5_7
    | ~ spl5_8
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f112,f60,f118,f114])).

fof(f118,plain,
    ( spl5_8
  <=> r2_hidden(sK1,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f60,plain,
    ( spl5_1
  <=> sK0 = k4_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f112,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK0,sK0))
    | k1_xboole_0 = k2_tarski(sK0,sK0)
    | ~ spl5_1 ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK1,k2_tarski(X0,X0))
        | k1_xboole_0 = k2_tarski(X0,X0) )
    | ~ spl5_1 ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK1,k2_tarski(X0,X0))
        | k1_xboole_0 = k2_tarski(X0,X0)
        | k1_xboole_0 = k2_tarski(X0,X0) )
    | ~ spl5_1 ),
    inference(superposition,[],[f99,f95])).

fof(f99,plain,
    ( ! [X0] :
        ( sK0 != sK3(X0)
        | ~ r2_hidden(sK1,X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_1 ),
    inference(superposition,[],[f34,f62])).

fof(f62,plain,
    ( sK0 = k4_tarski(sK1,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f34,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK3(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f91,plain,
    ( spl5_6
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f86,f82,f60,f88])).

fof(f82,plain,
    ( spl5_5
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f86,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(superposition,[],[f62,f84])).

fof(f84,plain,
    ( sK0 = sK2
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f85,plain,
    ( spl5_5
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f75,f69,f60,f82])).

fof(f69,plain,
    ( spl5_3
  <=> sK0 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f75,plain,
    ( sK0 = sK2
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f74,f71])).

fof(f71,plain,
    ( sK0 = k2_mcart_1(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f74,plain,
    ( k2_mcart_1(sK0) = sK2
    | ~ spl5_1 ),
    inference(superposition,[],[f32,f62])).

fof(f32,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f80,plain,
    ( spl5_4
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f73,f60,f77])).

fof(f77,plain,
    ( spl5_4
  <=> k1_mcart_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f73,plain,
    ( k1_mcart_1(sK0) = sK1
    | ~ spl5_1 ),
    inference(superposition,[],[f31,f62])).

fof(f31,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f72,plain,
    ( spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f30,f69,f65])).

fof(f65,plain,
    ( spl5_2
  <=> sK0 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f30,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK0
   => sK0 = k4_tarski(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f63,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f29,f60])).

fof(f29,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.09  % Command    : run_vampire %s %d
% 0.08/0.27  % Computer   : n011.cluster.edu
% 0.08/0.27  % Model      : x86_64 x86_64
% 0.08/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.27  % Memory     : 8042.1875MB
% 0.08/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.27  % CPULimit   : 60
% 0.08/0.27  % WCLimit    : 600
% 0.08/0.27  % DateTime   : Tue Dec  1 13:47:57 EST 2020
% 0.08/0.27  % CPUTime    : 
% 0.12/0.36  % (20027)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.12/0.36  % (20038)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.12/0.37  % (20030)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.12/0.37  % (20027)Refutation not found, incomplete strategy% (20027)------------------------------
% 0.12/0.37  % (20027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.37  % (20027)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.37  
% 0.12/0.37  % (20027)Memory used [KB]: 10618
% 0.12/0.37  % (20027)Time elapsed: 0.055 s
% 0.12/0.37  % (20027)------------------------------
% 0.12/0.37  % (20027)------------------------------
% 0.12/0.38  % (20038)Refutation found. Thanks to Tanya!
% 0.12/0.38  % SZS status Theorem for theBenchmark
% 0.12/0.38  % SZS output start Proof for theBenchmark
% 0.12/0.38  fof(f167,plain,(
% 0.12/0.38    $false),
% 0.12/0.38    inference(avatar_sat_refutation,[],[f63,f72,f80,f85,f91,f121,f127,f132,f144,f165])).
% 0.12/0.38  fof(f165,plain,(
% 0.12/0.38    ~spl5_7),
% 0.12/0.38    inference(avatar_contradiction_clause,[],[f164])).
% 0.12/0.38  fof(f164,plain,(
% 0.12/0.38    $false | ~spl5_7),
% 0.12/0.38    inference(subsumption_resolution,[],[f116,f154])).
% 0.12/0.38  fof(f154,plain,(
% 0.12/0.38    ( ! [X1] : (k1_xboole_0 != k2_tarski(X1,X1)) )),
% 0.12/0.38    inference(forward_demodulation,[],[f58,f96])).
% 0.12/0.38  fof(f96,plain,(
% 0.12/0.38    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 0.12/0.38    inference(superposition,[],[f51,f54])).
% 0.12/0.38  fof(f54,plain,(
% 0.12/0.38    ( ! [X0] : (k3_tarski(k2_tarski(X0,X0)) = X0) )),
% 0.12/0.38    inference(definition_unfolding,[],[f46,f45])).
% 0.12/0.38  fof(f45,plain,(
% 0.12/0.38    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.12/0.38    inference(cnf_transformation,[],[f9])).
% 0.12/0.38  fof(f9,axiom,(
% 0.12/0.38    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.12/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.12/0.38  fof(f46,plain,(
% 0.12/0.38    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.12/0.38    inference(cnf_transformation,[],[f16])).
% 0.12/0.38  fof(f16,plain,(
% 0.12/0.38    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.12/0.38    inference(rectify,[],[f1])).
% 0.12/0.38  fof(f1,axiom,(
% 0.12/0.38    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.12/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.12/0.38  fof(f51,plain,(
% 0.12/0.38    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))))) )),
% 0.12/0.38    inference(definition_unfolding,[],[f40,f44,f45])).
% 0.12/0.38  fof(f44,plain,(
% 0.12/0.38    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.12/0.38    inference(cnf_transformation,[],[f3])).
% 0.12/0.38  fof(f3,axiom,(
% 0.12/0.38    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.12/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.12/0.38  fof(f40,plain,(
% 0.12/0.38    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.12/0.38    inference(cnf_transformation,[],[f4])).
% 0.12/0.38  fof(f4,axiom,(
% 0.12/0.38    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.12/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.12/0.38  fof(f58,plain,(
% 0.12/0.38    ( ! [X1] : (k2_tarski(X1,X1) != k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)))) )),
% 0.12/0.38    inference(equality_resolution,[],[f53])).
% 0.12/0.38  fof(f53,plain,(
% 0.12/0.38    ( ! [X0,X1] : (X0 != X1 | k2_tarski(X0,X0) != k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)))) )),
% 0.12/0.38    inference(definition_unfolding,[],[f41,f43,f44,f43,f43])).
% 0.12/0.38  fof(f43,plain,(
% 0.12/0.38    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.12/0.38    inference(cnf_transformation,[],[f6])).
% 0.12/0.38  fof(f6,axiom,(
% 0.12/0.38    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.12/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.12/0.38  fof(f41,plain,(
% 0.12/0.38    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.12/0.38    inference(cnf_transformation,[],[f28])).
% 0.12/0.38  fof(f28,plain,(
% 0.12/0.38    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.12/0.38    inference(nnf_transformation,[],[f10])).
% 0.12/0.38  fof(f10,axiom,(
% 0.12/0.38    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.12/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.12/0.38  fof(f116,plain,(
% 0.12/0.38    k1_xboole_0 = k2_tarski(sK0,sK0) | ~spl5_7),
% 0.12/0.38    inference(avatar_component_clause,[],[f114])).
% 0.12/0.38  fof(f114,plain,(
% 0.12/0.38    spl5_7 <=> k1_xboole_0 = k2_tarski(sK0,sK0)),
% 0.12/0.38    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.12/0.38  fof(f144,plain,(
% 0.12/0.38    k1_mcart_1(sK0) != sK1 | sK0 != k1_mcart_1(sK0) | r2_hidden(sK1,k2_tarski(sK0,sK0)) | ~r2_hidden(sK0,k2_tarski(sK0,sK0))),
% 0.12/0.38    introduced(theory_tautology_sat_conflict,[])).
% 0.12/0.38  fof(f132,plain,(
% 0.12/0.38    spl5_9),
% 0.12/0.38    inference(avatar_contradiction_clause,[],[f129])).
% 0.12/0.38  fof(f129,plain,(
% 0.12/0.38    $false | spl5_9),
% 0.12/0.38    inference(unit_resulting_resolution,[],[f56,f126])).
% 0.12/0.38  fof(f126,plain,(
% 0.12/0.38    ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | spl5_9),
% 0.12/0.38    inference(avatar_component_clause,[],[f124])).
% 0.12/0.38  fof(f124,plain,(
% 0.12/0.38    spl5_9 <=> r2_hidden(sK0,k2_tarski(sK0,sK0))),
% 0.12/0.38    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.12/0.38  fof(f56,plain,(
% 0.12/0.38    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 0.12/0.38    inference(equality_resolution,[],[f55])).
% 0.12/0.38  fof(f55,plain,(
% 0.12/0.38    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 0.12/0.38    inference(equality_resolution,[],[f49])).
% 0.12/0.38  fof(f49,plain,(
% 0.12/0.38    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 0.12/0.38    inference(definition_unfolding,[],[f37,f43])).
% 0.12/0.38  fof(f37,plain,(
% 0.12/0.38    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.12/0.38    inference(cnf_transformation,[],[f27])).
% 0.12/0.38  fof(f27,plain,(
% 0.12/0.38    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.12/0.38    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).
% 0.12/0.38  fof(f26,plain,(
% 0.12/0.38    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 0.12/0.38    introduced(choice_axiom,[])).
% 0.12/0.38  fof(f25,plain,(
% 0.12/0.38    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.12/0.38    inference(rectify,[],[f24])).
% 0.12/0.38  fof(f24,plain,(
% 0.12/0.38    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.12/0.38    inference(nnf_transformation,[],[f5])).
% 0.12/0.38  fof(f5,axiom,(
% 0.12/0.38    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.12/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.12/0.38  fof(f127,plain,(
% 0.12/0.38    spl5_7 | ~spl5_9 | ~spl5_6),
% 0.12/0.38    inference(avatar_split_clause,[],[f122,f88,f124,f114])).
% 0.12/0.38  fof(f88,plain,(
% 0.12/0.38    spl5_6 <=> sK0 = k4_tarski(sK1,sK0)),
% 0.12/0.38    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.12/0.38  fof(f122,plain,(
% 0.12/0.38    ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | k1_xboole_0 = k2_tarski(sK0,sK0) | ~spl5_6),
% 0.12/0.38    inference(equality_resolution,[],[f111])).
% 0.12/0.38  fof(f111,plain,(
% 0.12/0.38    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK0,k2_tarski(X0,X0)) | k1_xboole_0 = k2_tarski(X0,X0)) ) | ~spl5_6),
% 0.12/0.38    inference(duplicate_literal_removal,[],[f110])).
% 0.12/0.38  fof(f110,plain,(
% 0.12/0.38    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK0,k2_tarski(X0,X0)) | k1_xboole_0 = k2_tarski(X0,X0) | k1_xboole_0 = k2_tarski(X0,X0)) ) | ~spl5_6),
% 0.12/0.38    inference(superposition,[],[f106,f95])).
% 0.12/0.38  fof(f95,plain,(
% 0.12/0.38    ( ! [X1] : (sK3(k2_tarski(X1,X1)) = X1 | k1_xboole_0 = k2_tarski(X1,X1)) )),
% 0.12/0.38    inference(resolution,[],[f57,f33])).
% 0.12/0.38  fof(f33,plain,(
% 0.12/0.38    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.12/0.38    inference(cnf_transformation,[],[f23])).
% 0.12/0.38  fof(f23,plain,(
% 0.12/0.38    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 0.12/0.38    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f22])).
% 0.12/0.38  fof(f22,plain,(
% 0.12/0.38    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 0.12/0.38    introduced(choice_axiom,[])).
% 0.12/0.38  fof(f18,plain,(
% 0.12/0.38    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.12/0.38    inference(ennf_transformation,[],[f13])).
% 0.12/0.38  fof(f13,axiom,(
% 0.12/0.38    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.12/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.12/0.38  fof(f57,plain,(
% 0.12/0.38    ( ! [X0,X3] : (~r2_hidden(X3,k2_tarski(X0,X0)) | X0 = X3) )),
% 0.12/0.38    inference(equality_resolution,[],[f50])).
% 0.12/0.38  fof(f50,plain,(
% 0.12/0.38    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 0.12/0.38    inference(definition_unfolding,[],[f36,f43])).
% 0.12/0.38  fof(f36,plain,(
% 0.12/0.38    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.12/0.38    inference(cnf_transformation,[],[f27])).
% 0.12/0.38  fof(f106,plain,(
% 0.12/0.38    ( ! [X1] : (sK0 != sK3(X1) | ~r2_hidden(sK0,X1) | k1_xboole_0 = X1) ) | ~spl5_6),
% 0.12/0.38    inference(superposition,[],[f35,f90])).
% 0.12/0.38  fof(f90,plain,(
% 0.12/0.38    sK0 = k4_tarski(sK1,sK0) | ~spl5_6),
% 0.12/0.38    inference(avatar_component_clause,[],[f88])).
% 0.12/0.38  fof(f35,plain,(
% 0.12/0.38    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK3(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.12/0.38    inference(cnf_transformation,[],[f23])).
% 0.12/0.38  fof(f121,plain,(
% 0.12/0.38    spl5_7 | ~spl5_8 | ~spl5_1),
% 0.12/0.38    inference(avatar_split_clause,[],[f112,f60,f118,f114])).
% 0.12/0.38  fof(f118,plain,(
% 0.12/0.38    spl5_8 <=> r2_hidden(sK1,k2_tarski(sK0,sK0))),
% 0.12/0.38    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.12/0.38  fof(f60,plain,(
% 0.12/0.38    spl5_1 <=> sK0 = k4_tarski(sK1,sK2)),
% 0.12/0.38    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.12/0.38  fof(f112,plain,(
% 0.12/0.38    ~r2_hidden(sK1,k2_tarski(sK0,sK0)) | k1_xboole_0 = k2_tarski(sK0,sK0) | ~spl5_1),
% 0.12/0.38    inference(equality_resolution,[],[f104])).
% 0.12/0.38  fof(f104,plain,(
% 0.12/0.38    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK1,k2_tarski(X0,X0)) | k1_xboole_0 = k2_tarski(X0,X0)) ) | ~spl5_1),
% 0.12/0.38    inference(duplicate_literal_removal,[],[f103])).
% 0.12/0.38  fof(f103,plain,(
% 0.12/0.38    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK1,k2_tarski(X0,X0)) | k1_xboole_0 = k2_tarski(X0,X0) | k1_xboole_0 = k2_tarski(X0,X0)) ) | ~spl5_1),
% 0.12/0.38    inference(superposition,[],[f99,f95])).
% 0.12/0.38  fof(f99,plain,(
% 0.12/0.38    ( ! [X0] : (sK0 != sK3(X0) | ~r2_hidden(sK1,X0) | k1_xboole_0 = X0) ) | ~spl5_1),
% 0.12/0.38    inference(superposition,[],[f34,f62])).
% 0.12/0.38  fof(f62,plain,(
% 0.12/0.38    sK0 = k4_tarski(sK1,sK2) | ~spl5_1),
% 0.12/0.38    inference(avatar_component_clause,[],[f60])).
% 0.12/0.38  fof(f34,plain,(
% 0.12/0.38    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK3(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.12/0.38    inference(cnf_transformation,[],[f23])).
% 0.12/0.38  fof(f91,plain,(
% 0.12/0.38    spl5_6 | ~spl5_1 | ~spl5_5),
% 0.12/0.38    inference(avatar_split_clause,[],[f86,f82,f60,f88])).
% 0.12/0.38  fof(f82,plain,(
% 0.12/0.38    spl5_5 <=> sK0 = sK2),
% 0.12/0.38    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.12/0.38  fof(f86,plain,(
% 0.12/0.38    sK0 = k4_tarski(sK1,sK0) | (~spl5_1 | ~spl5_5)),
% 0.12/0.38    inference(superposition,[],[f62,f84])).
% 0.12/0.38  fof(f84,plain,(
% 0.12/0.38    sK0 = sK2 | ~spl5_5),
% 0.12/0.38    inference(avatar_component_clause,[],[f82])).
% 0.12/0.38  fof(f85,plain,(
% 0.12/0.38    spl5_5 | ~spl5_1 | ~spl5_3),
% 0.12/0.38    inference(avatar_split_clause,[],[f75,f69,f60,f82])).
% 0.12/0.38  fof(f69,plain,(
% 0.12/0.38    spl5_3 <=> sK0 = k2_mcart_1(sK0)),
% 0.12/0.38    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.12/0.38  fof(f75,plain,(
% 0.12/0.38    sK0 = sK2 | (~spl5_1 | ~spl5_3)),
% 0.12/0.38    inference(forward_demodulation,[],[f74,f71])).
% 0.12/0.38  fof(f71,plain,(
% 0.12/0.38    sK0 = k2_mcart_1(sK0) | ~spl5_3),
% 0.12/0.38    inference(avatar_component_clause,[],[f69])).
% 0.12/0.38  fof(f74,plain,(
% 0.12/0.38    k2_mcart_1(sK0) = sK2 | ~spl5_1),
% 0.12/0.38    inference(superposition,[],[f32,f62])).
% 0.12/0.38  fof(f32,plain,(
% 0.12/0.38    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.12/0.38    inference(cnf_transformation,[],[f12])).
% 0.12/0.38  fof(f12,axiom,(
% 0.12/0.38    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.12/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.12/0.38  fof(f80,plain,(
% 0.12/0.38    spl5_4 | ~spl5_1),
% 0.12/0.38    inference(avatar_split_clause,[],[f73,f60,f77])).
% 0.12/0.38  fof(f77,plain,(
% 0.12/0.38    spl5_4 <=> k1_mcart_1(sK0) = sK1),
% 0.12/0.38    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.12/0.38  fof(f73,plain,(
% 0.12/0.38    k1_mcart_1(sK0) = sK1 | ~spl5_1),
% 0.12/0.38    inference(superposition,[],[f31,f62])).
% 0.12/0.38  fof(f31,plain,(
% 0.12/0.38    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.12/0.38    inference(cnf_transformation,[],[f12])).
% 0.12/0.38  fof(f72,plain,(
% 0.12/0.38    spl5_2 | spl5_3),
% 0.12/0.38    inference(avatar_split_clause,[],[f30,f69,f65])).
% 0.12/0.38  fof(f65,plain,(
% 0.12/0.38    spl5_2 <=> sK0 = k1_mcart_1(sK0)),
% 0.12/0.38    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.12/0.38  fof(f30,plain,(
% 0.12/0.38    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 0.12/0.38    inference(cnf_transformation,[],[f21])).
% 0.12/0.38  fof(f21,plain,(
% 0.12/0.38    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & sK0 = k4_tarski(sK1,sK2)),
% 0.12/0.38    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f20,f19])).
% 0.12/0.38  fof(f19,plain,(
% 0.12/0.38    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & ? [X2,X1] : k4_tarski(X1,X2) = sK0)),
% 0.12/0.38    introduced(choice_axiom,[])).
% 0.12/0.38  fof(f20,plain,(
% 0.12/0.38    ? [X2,X1] : k4_tarski(X1,X2) = sK0 => sK0 = k4_tarski(sK1,sK2)),
% 0.12/0.38    introduced(choice_axiom,[])).
% 0.12/0.38  fof(f17,plain,(
% 0.12/0.38    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.12/0.38    inference(ennf_transformation,[],[f15])).
% 0.12/0.38  fof(f15,negated_conjecture,(
% 0.12/0.38    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.12/0.38    inference(negated_conjecture,[],[f14])).
% 0.12/0.38  fof(f14,conjecture,(
% 0.12/0.38    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.12/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.12/0.38  fof(f63,plain,(
% 0.12/0.38    spl5_1),
% 0.12/0.38    inference(avatar_split_clause,[],[f29,f60])).
% 0.12/0.38  fof(f29,plain,(
% 0.12/0.38    sK0 = k4_tarski(sK1,sK2)),
% 0.12/0.38    inference(cnf_transformation,[],[f21])).
% 0.12/0.38  % SZS output end Proof for theBenchmark
% 0.12/0.38  % (20038)------------------------------
% 0.12/0.38  % (20038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.38  % (20038)Termination reason: Refutation
% 0.12/0.38  
% 0.12/0.38  % (20038)Memory used [KB]: 10746
% 0.12/0.38  % (20038)Time elapsed: 0.041 s
% 0.12/0.38  % (20038)------------------------------
% 0.12/0.38  % (20038)------------------------------
% 0.12/0.38  % (20022)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.12/0.38  % (20014)Success in time 0.099 s
%------------------------------------------------------------------------------
