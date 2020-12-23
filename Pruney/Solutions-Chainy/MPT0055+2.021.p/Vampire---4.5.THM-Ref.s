%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 156 expanded)
%              Number of leaves         :   13 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  213 ( 735 expanded)
%              Number of equality atoms :   33 ( 112 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f370,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f213,f214,f218,f338,f340,f367,f369])).

fof(f369,plain,
    ( ~ spl4_9
    | spl4_7 ),
    inference(avatar_split_clause,[],[f368,f102,f116])).

fof(f116,plain,
    ( spl4_9
  <=> r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f102,plain,
    ( spl4_7
  <=> r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f368,plain,
    ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl4_7 ),
    inference(subsumption_resolution,[],[f111,f103])).

fof(f103,plain,
    ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f111,plain,
    ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X1] :
      ( k3_xboole_0(sK0,sK1) != X1
      | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1))
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),X1) ) ),
    inference(superposition,[],[f30,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
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

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f30,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f20])).

fof(f20,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f367,plain,
    ( spl4_9
    | spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f363,f106,f102,f116])).

fof(f106,plain,
    ( spl4_8
  <=> r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f363,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl4_7
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f356,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f356,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | spl4_7
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f108,f103,f56])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f108,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f340,plain,
    ( ~ spl4_7
    | ~ spl4_8
    | spl4_9 ),
    inference(avatar_split_clause,[],[f339,f116,f106,f102])).

fof(f339,plain,
    ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | spl4_9 ),
    inference(subsumption_resolution,[],[f113,f117])).

fof(f117,plain,
    ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f113,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2] :
      ( k3_xboole_0(sK0,sK1) != X2
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X2),k4_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X2),sK0)
      | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X2),X2) ) ),
    inference(superposition,[],[f30,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f338,plain,(
    ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f34,f217])).

fof(f217,plain,
    ( ! [X6] : ~ r1_tarski(X6,k3_xboole_0(sK0,sK1))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl4_12
  <=> ! [X6] : ~ r1_tarski(X6,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f218,plain,
    ( spl4_12
    | ~ spl4_11
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f189,f102,f172,f216])).

fof(f172,plain,
    ( spl4_11
  <=> r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f189,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0)
        | ~ r1_tarski(X6,k3_xboole_0(sK0,sK1)) )
    | ~ spl4_7 ),
    inference(superposition,[],[f134,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f31])).

fof(f31,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f134,plain,
    ( ! [X0] : ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1)))
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f104,f57])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f104,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f214,plain,
    ( ~ spl4_9
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f185,f102,f116])).

fof(f185,plain,
    ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl4_7 ),
    inference(superposition,[],[f134,f37])).

fof(f213,plain,
    ( ~ spl4_7
    | spl4_8
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | ~ spl4_7
    | spl4_8
    | spl4_11 ),
    inference(subsumption_resolution,[],[f211,f34])).

fof(f211,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ spl4_7
    | spl4_8
    | spl4_11 ),
    inference(subsumption_resolution,[],[f210,f174])).

fof(f174,plain,
    ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f172])).

fof(f210,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0)
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ spl4_7
    | spl4_8 ),
    inference(superposition,[],[f135,f55])).

fof(f135,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0))
    | ~ spl4_7
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f107,f104,f56])).

fof(f107,plain,
    ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f109,plain,
    ( spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f100,f106,f102])).

fof(f100,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( k3_xboole_0(sK0,sK1) != X0
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),sK0)
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f30,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:11:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (10982)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (10974)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (10976)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (10982)Refutation not found, incomplete strategy% (10982)------------------------------
% 0.20/0.50  % (10982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (10976)Refutation not found, incomplete strategy% (10976)------------------------------
% 0.20/0.50  % (10976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (10995)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (10975)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (10998)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (10976)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (10976)Memory used [KB]: 10618
% 0.20/0.51  % (10976)Time elapsed: 0.097 s
% 0.20/0.51  % (10976)------------------------------
% 0.20/0.51  % (10976)------------------------------
% 0.20/0.51  % (10982)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (10982)Memory used [KB]: 10618
% 0.20/0.51  % (10982)Time elapsed: 0.095 s
% 0.20/0.51  % (10982)------------------------------
% 0.20/0.51  % (10982)------------------------------
% 0.20/0.51  % (11001)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (10974)Refutation not found, incomplete strategy% (10974)------------------------------
% 0.20/0.51  % (10974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (10974)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (10974)Memory used [KB]: 1663
% 0.20/0.51  % (10974)Time elapsed: 0.101 s
% 0.20/0.51  % (10974)------------------------------
% 0.20/0.51  % (10974)------------------------------
% 0.20/0.52  % (10985)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (10986)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (10980)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (10985)Refutation not found, incomplete strategy% (10985)------------------------------
% 0.20/0.52  % (10985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10985)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10985)Memory used [KB]: 10618
% 0.20/0.52  % (10985)Time elapsed: 0.114 s
% 0.20/0.52  % (10985)------------------------------
% 0.20/0.52  % (10985)------------------------------
% 0.20/0.52  % (10981)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (10995)Refutation not found, incomplete strategy% (10995)------------------------------
% 0.20/0.53  % (10995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (10995)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (10995)Memory used [KB]: 1663
% 0.20/0.53  % (10995)Time elapsed: 0.127 s
% 0.20/0.53  % (10995)------------------------------
% 0.20/0.53  % (10995)------------------------------
% 0.20/0.53  % (10991)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (10989)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (10988)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (10997)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (10989)Refutation not found, incomplete strategy% (10989)------------------------------
% 0.20/0.54  % (10989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (10989)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (10989)Memory used [KB]: 6140
% 0.20/0.54  % (10989)Time elapsed: 0.003 s
% 0.20/0.54  % (10989)------------------------------
% 0.20/0.54  % (10989)------------------------------
% 0.20/0.54  % (10991)Refutation not found, incomplete strategy% (10991)------------------------------
% 0.20/0.54  % (10991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (10991)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (10991)Memory used [KB]: 10618
% 0.20/0.54  % (10991)Time elapsed: 0.125 s
% 0.20/0.54  % (10991)------------------------------
% 0.20/0.54  % (10991)------------------------------
% 0.20/0.54  % (10984)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (10983)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (10984)Refutation not found, incomplete strategy% (10984)------------------------------
% 0.20/0.54  % (10984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (10984)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (10984)Memory used [KB]: 10618
% 0.20/0.54  % (10984)Time elapsed: 0.135 s
% 0.20/0.54  % (10984)------------------------------
% 0.20/0.54  % (10984)------------------------------
% 0.20/0.54  % (10983)Refutation not found, incomplete strategy% (10983)------------------------------
% 0.20/0.54  % (10983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (10983)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (10983)Memory used [KB]: 10618
% 0.20/0.54  % (10983)Time elapsed: 0.136 s
% 0.20/0.54  % (10983)------------------------------
% 0.20/0.54  % (10983)------------------------------
% 0.20/0.54  % (10978)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.55  % (10978)Refutation not found, incomplete strategy% (10978)------------------------------
% 0.20/0.55  % (10978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (10978)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (10978)Memory used [KB]: 6140
% 0.20/0.55  % (10978)Time elapsed: 0.146 s
% 0.20/0.55  % (10978)------------------------------
% 0.20/0.55  % (10978)------------------------------
% 0.20/0.55  % (11003)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (10994)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (11002)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (10996)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.55  % (10977)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.56  % (11000)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.56  % (10987)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.56  % (10999)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.56  % (10999)Refutation not found, incomplete strategy% (10999)------------------------------
% 0.20/0.56  % (10999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (10999)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (10999)Memory used [KB]: 6140
% 0.20/0.56  % (10999)Time elapsed: 0.161 s
% 0.20/0.56  % (10999)------------------------------
% 0.20/0.56  % (10999)------------------------------
% 0.20/0.56  % (10990)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.56  % (10993)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.56  % (10979)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.57  % (10992)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.57  % (10994)Refutation not found, incomplete strategy% (10994)------------------------------
% 0.20/0.57  % (10994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (10994)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (10994)Memory used [KB]: 10618
% 0.20/0.57  % (10994)Time elapsed: 0.171 s
% 0.20/0.57  % (10994)------------------------------
% 0.20/0.57  % (10994)------------------------------
% 0.20/0.57  % (10996)Refutation not found, incomplete strategy% (10996)------------------------------
% 0.20/0.57  % (10996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (10996)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (10996)Memory used [KB]: 10618
% 0.20/0.57  % (10996)Time elapsed: 0.122 s
% 0.20/0.57  % (10996)------------------------------
% 0.20/0.57  % (10996)------------------------------
% 0.20/0.60  % (11000)Refutation found. Thanks to Tanya!
% 0.20/0.60  % SZS status Theorem for theBenchmark
% 0.20/0.60  % SZS output start Proof for theBenchmark
% 0.20/0.60  fof(f370,plain,(
% 0.20/0.60    $false),
% 0.20/0.60    inference(avatar_sat_refutation,[],[f109,f213,f214,f218,f338,f340,f367,f369])).
% 0.20/0.60  fof(f369,plain,(
% 0.20/0.60    ~spl4_9 | spl4_7),
% 0.20/0.60    inference(avatar_split_clause,[],[f368,f102,f116])).
% 0.20/0.60  fof(f116,plain,(
% 0.20/0.60    spl4_9 <=> r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.60  fof(f102,plain,(
% 0.20/0.60    spl4_7 <=> r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.60  fof(f368,plain,(
% 0.20/0.60    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | spl4_7),
% 0.20/0.60    inference(subsumption_resolution,[],[f111,f103])).
% 0.20/0.60  fof(f103,plain,(
% 0.20/0.60    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | spl4_7),
% 0.20/0.60    inference(avatar_component_clause,[],[f102])).
% 0.20/0.60  fof(f111,plain,(
% 0.20/0.60    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 0.20/0.60    inference(equality_resolution,[],[f64])).
% 0.20/0.60  fof(f64,plain,(
% 0.20/0.60    ( ! [X1] : (k3_xboole_0(sK0,sK1) != X1 | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),X1)) )),
% 0.20/0.60    inference(superposition,[],[f30,f49])).
% 0.20/0.60  fof(f49,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f29])).
% 0.20/0.60  fof(f29,plain,(
% 0.20/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 0.20/0.60  fof(f28,plain,(
% 0.20/0.60    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.20/0.60    introduced(choice_axiom,[])).
% 0.20/0.60  fof(f27,plain,(
% 0.20/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.60    inference(rectify,[],[f26])).
% 0.20/0.60  fof(f26,plain,(
% 0.20/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.60    inference(flattening,[],[f25])).
% 0.20/0.60  fof(f25,plain,(
% 0.20/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.60    inference(nnf_transformation,[],[f3])).
% 0.20/0.60  fof(f3,axiom,(
% 0.20/0.60    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.60  fof(f30,plain,(
% 0.20/0.60    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.60    inference(cnf_transformation,[],[f21])).
% 0.20/0.60  fof(f21,plain,(
% 0.20/0.60    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f20])).
% 0.20/0.60  fof(f20,plain,(
% 0.20/0.60    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.60    introduced(choice_axiom,[])).
% 0.20/0.60  fof(f17,plain,(
% 0.20/0.60    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.60    inference(ennf_transformation,[],[f14])).
% 0.20/0.60  fof(f14,negated_conjecture,(
% 0.20/0.60    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.60    inference(negated_conjecture,[],[f13])).
% 0.20/0.60  fof(f13,conjecture,(
% 0.20/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.60  fof(f367,plain,(
% 0.20/0.60    spl4_9 | spl4_7 | ~spl4_8),
% 0.20/0.60    inference(avatar_split_clause,[],[f363,f106,f102,f116])).
% 0.20/0.60  fof(f106,plain,(
% 0.20/0.60    spl4_8 <=> r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.60  fof(f363,plain,(
% 0.20/0.60    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | (spl4_7 | ~spl4_8)),
% 0.20/0.60    inference(forward_demodulation,[],[f356,f37])).
% 0.20/0.60  fof(f37,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.60    inference(cnf_transformation,[],[f12])).
% 0.20/0.60  fof(f12,axiom,(
% 0.20/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.60  fof(f356,plain,(
% 0.20/0.60    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))) | (spl4_7 | ~spl4_8)),
% 0.20/0.60    inference(unit_resulting_resolution,[],[f108,f103,f56])).
% 0.20/0.60  fof(f56,plain,(
% 0.20/0.60    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.20/0.60    inference(equality_resolution,[],[f47])).
% 0.20/0.60  fof(f47,plain,(
% 0.20/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.60    inference(cnf_transformation,[],[f29])).
% 0.20/0.60  fof(f108,plain,(
% 0.20/0.60    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~spl4_8),
% 0.20/0.60    inference(avatar_component_clause,[],[f106])).
% 1.87/0.60  fof(f340,plain,(
% 1.87/0.60    ~spl4_7 | ~spl4_8 | spl4_9),
% 1.87/0.60    inference(avatar_split_clause,[],[f339,f116,f106,f102])).
% 1.87/0.60  fof(f339,plain,(
% 1.87/0.60    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | spl4_9),
% 1.87/0.60    inference(subsumption_resolution,[],[f113,f117])).
% 1.87/0.60  fof(f117,plain,(
% 1.87/0.60    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | spl4_9),
% 1.87/0.60    inference(avatar_component_clause,[],[f116])).
% 1.87/0.60  fof(f113,plain,(
% 1.87/0.60    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 1.87/0.60    inference(equality_resolution,[],[f65])).
% 1.87/0.60  fof(f65,plain,(
% 1.87/0.60    ( ! [X2] : (k3_xboole_0(sK0,sK1) != X2 | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X2),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X2),sK0) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X2),X2)) )),
% 1.87/0.60    inference(superposition,[],[f30,f50])).
% 1.87/0.60  fof(f50,plain,(
% 1.87/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f29])).
% 1.87/0.60  fof(f338,plain,(
% 1.87/0.60    ~spl4_12),
% 1.87/0.60    inference(avatar_contradiction_clause,[],[f336])).
% 1.87/0.60  fof(f336,plain,(
% 1.87/0.60    $false | ~spl4_12),
% 1.87/0.60    inference(unit_resulting_resolution,[],[f34,f217])).
% 1.87/0.60  fof(f217,plain,(
% 1.87/0.60    ( ! [X6] : (~r1_tarski(X6,k3_xboole_0(sK0,sK1))) ) | ~spl4_12),
% 1.87/0.60    inference(avatar_component_clause,[],[f216])).
% 1.87/0.60  fof(f216,plain,(
% 1.87/0.60    spl4_12 <=> ! [X6] : ~r1_tarski(X6,k3_xboole_0(sK0,sK1))),
% 1.87/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.87/0.60  fof(f34,plain,(
% 1.87/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f7])).
% 1.87/0.60  fof(f7,axiom,(
% 1.87/0.60    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.87/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.87/0.60  fof(f218,plain,(
% 1.87/0.60    spl4_12 | ~spl4_11 | ~spl4_7),
% 1.87/0.60    inference(avatar_split_clause,[],[f189,f102,f172,f216])).
% 1.87/0.60  fof(f172,plain,(
% 1.87/0.60    spl4_11 <=> r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0)),
% 1.87/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.87/0.60  fof(f189,plain,(
% 1.87/0.60    ( ! [X6] : (~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0) | ~r1_tarski(X6,k3_xboole_0(sK0,sK1))) ) | ~spl4_7),
% 1.87/0.60    inference(superposition,[],[f134,f55])).
% 1.87/0.60  fof(f55,plain,(
% 1.87/0.60    ( ! [X0,X1] : (o_0_0_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.87/0.60    inference(definition_unfolding,[],[f44,f31])).
% 1.87/0.60  fof(f31,plain,(
% 1.87/0.60    k1_xboole_0 = o_0_0_xboole_0),
% 1.87/0.60    inference(cnf_transformation,[],[f2])).
% 1.87/0.60  fof(f2,axiom,(
% 1.87/0.60    k1_xboole_0 = o_0_0_xboole_0),
% 1.87/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).
% 1.87/0.60  fof(f44,plain,(
% 1.87/0.60    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f19])).
% 1.87/0.60  fof(f19,plain,(
% 1.87/0.60    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 1.87/0.60    inference(ennf_transformation,[],[f16])).
% 1.87/0.60  fof(f16,plain,(
% 1.87/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 1.87/0.60    inference(unused_predicate_definition_removal,[],[f6])).
% 1.87/0.60  fof(f6,axiom,(
% 1.87/0.60    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.87/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.87/0.60  fof(f134,plain,(
% 1.87/0.60    ( ! [X0] : (~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1)))) ) | ~spl4_7),
% 1.87/0.60    inference(unit_resulting_resolution,[],[f104,f57])).
% 1.87/0.60  fof(f57,plain,(
% 1.87/0.60    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.87/0.60    inference(equality_resolution,[],[f46])).
% 1.87/0.60  fof(f46,plain,(
% 1.87/0.60    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.87/0.60    inference(cnf_transformation,[],[f29])).
% 1.87/0.60  fof(f104,plain,(
% 1.87/0.60    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~spl4_7),
% 1.87/0.60    inference(avatar_component_clause,[],[f102])).
% 1.87/0.60  fof(f214,plain,(
% 1.87/0.60    ~spl4_9 | ~spl4_7),
% 1.87/0.60    inference(avatar_split_clause,[],[f185,f102,f116])).
% 1.87/0.60  fof(f185,plain,(
% 1.87/0.60    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl4_7),
% 1.87/0.60    inference(superposition,[],[f134,f37])).
% 1.87/0.60  fof(f213,plain,(
% 1.87/0.60    ~spl4_7 | spl4_8 | spl4_11),
% 1.87/0.60    inference(avatar_contradiction_clause,[],[f212])).
% 1.87/0.60  fof(f212,plain,(
% 1.87/0.60    $false | (~spl4_7 | spl4_8 | spl4_11)),
% 1.87/0.60    inference(subsumption_resolution,[],[f211,f34])).
% 1.87/0.60  fof(f211,plain,(
% 1.87/0.60    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | (~spl4_7 | spl4_8 | spl4_11)),
% 1.87/0.60    inference(subsumption_resolution,[],[f210,f174])).
% 1.87/0.60  fof(f174,plain,(
% 1.87/0.60    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0) | spl4_11),
% 1.87/0.60    inference(avatar_component_clause,[],[f172])).
% 1.87/0.60  fof(f210,plain,(
% 1.87/0.60    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | (~spl4_7 | spl4_8)),
% 1.87/0.60    inference(superposition,[],[f135,f55])).
% 1.87/0.60  fof(f135,plain,(
% 1.87/0.60    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0)) | (~spl4_7 | spl4_8)),
% 1.87/0.60    inference(unit_resulting_resolution,[],[f107,f104,f56])).
% 1.87/0.60  fof(f107,plain,(
% 1.87/0.60    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | spl4_8),
% 1.87/0.60    inference(avatar_component_clause,[],[f106])).
% 1.87/0.60  fof(f109,plain,(
% 1.87/0.60    spl4_7 | spl4_8),
% 1.87/0.60    inference(avatar_split_clause,[],[f100,f106,f102])).
% 1.87/0.60  fof(f100,plain,(
% 1.87/0.60    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 1.87/0.60    inference(equality_resolution,[],[f63])).
% 1.87/0.60  fof(f63,plain,(
% 1.87/0.60    ( ! [X0] : (k3_xboole_0(sK0,sK1) != X0 | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),sK0) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),X0)) )),
% 1.87/0.60    inference(superposition,[],[f30,f48])).
% 1.87/0.60  fof(f48,plain,(
% 1.87/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f29])).
% 1.87/0.60  % SZS output end Proof for theBenchmark
% 1.87/0.60  % (11000)------------------------------
% 1.87/0.60  % (11000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.60  % (11000)Termination reason: Refutation
% 1.87/0.60  
% 1.87/0.60  % (11000)Memory used [KB]: 10874
% 1.87/0.60  % (11000)Time elapsed: 0.203 s
% 1.87/0.60  % (11000)------------------------------
% 1.87/0.60  % (11000)------------------------------
% 1.87/0.60  % (10973)Success in time 0.237 s
%------------------------------------------------------------------------------
