%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 162 expanded)
%              Number of leaves         :   22 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  283 ( 550 expanded)
%              Number of equality atoms :   33 (  51 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f629,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f74,f79,f93,f102,f118,f150,f338,f395,f628])).

fof(f628,plain,
    ( spl5_4
    | ~ spl5_8
    | ~ spl5_12
    | spl5_23 ),
    inference(avatar_contradiction_clause,[],[f627])).

fof(f627,plain,
    ( $false
    | spl5_4
    | ~ spl5_8
    | ~ spl5_12
    | spl5_23 ),
    inference(subsumption_resolution,[],[f626,f393])).

fof(f393,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | spl5_23 ),
    inference(avatar_component_clause,[],[f391])).

fof(f391,plain,
    ( spl5_23
  <=> r2_hidden(sK3(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f626,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | spl5_4
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f625,f100])).

fof(f100,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl5_8
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f625,plain,
    ( r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | spl5_4
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f624,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f624,plain,
    ( r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)))
    | spl5_4
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f585,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f585,plain,
    ( r2_hidden(sK3(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1))
    | spl5_4
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f73,f175,f46])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f175,plain,
    ( r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK0,sK2))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl5_12
  <=> r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f73,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl5_4
  <=> r2_hidden(sK3(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f395,plain,
    ( ~ spl5_23
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f381,f115,f98,f391])).

fof(f115,plain,
    ( spl5_9
  <=> r2_hidden(sK3(sK0,sK1),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f381,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(resolution,[],[f162,f117])).

fof(f117,plain,
    ( r2_hidden(sK3(sK0,sK1),k2_xboole_0(sK1,sK2))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f162,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k2_xboole_0(sK1,sK2))
        | ~ r2_hidden(X5,k1_xboole_0) )
    | ~ spl5_8 ),
    inference(superposition,[],[f47,f100])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f338,plain,
    ( spl5_12
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f333,f147,f76,f173])).

fof(f76,plain,
    ( spl5_5
  <=> r2_hidden(sK3(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f147,plain,
    ( spl5_11
  <=> r1_tarski(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f333,plain,
    ( r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK0,sK2))
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(resolution,[],[f113,f149])).

fof(f149,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f147])).

fof(f113,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK0,X2)
        | r2_hidden(sK3(sK0,sK1),X2) )
    | ~ spl5_5 ),
    inference(resolution,[],[f78,f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f78,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f150,plain,
    ( spl5_11
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f129,f89,f147])).

fof(f89,plain,
    ( spl5_7
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f129,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f91,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f91,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f118,plain,
    ( spl5_9
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f109,f76,f60,f115])).

fof(f60,plain,
    ( spl5_3
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f109,plain,
    ( r2_hidden(sK3(sK0,sK1),k2_xboole_0(sK1,sK2))
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f62,f78,f33])).

fof(f62,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f102,plain,
    ( spl5_8
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f95,f60,f98])).

fof(f95,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_3 ),
    inference(resolution,[],[f62,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f93,plain,
    ( spl5_7
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f87,f55,f89])).

fof(f55,plain,
    ( spl5_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f87,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl5_2 ),
    inference(resolution,[],[f57,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f57,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f79,plain,
    ( spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f65,f50,f76])).

fof(f50,plain,
    ( spl5_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f65,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f52,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f74,plain,
    ( ~ spl5_4
    | spl5_1 ),
    inference(avatar_split_clause,[],[f66,f50,f71])).

fof(f66,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK1)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f52,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f27,f60])).

fof(f27,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f58,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f28,f55])).

fof(f28,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f29,f50])).

fof(f29,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:14:20 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (1749)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (1757)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (1754)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (1755)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (1752)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (1771)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (1773)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (1753)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (1750)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (1763)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (1765)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (1777)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (1767)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (1774)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (1751)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (1767)Refutation not found, incomplete strategy% (1767)------------------------------
% 0.22/0.54  % (1767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1767)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (1767)Memory used [KB]: 10618
% 0.22/0.54  % (1767)Time elapsed: 0.128 s
% 0.22/0.54  % (1767)------------------------------
% 0.22/0.54  % (1767)------------------------------
% 0.22/0.54  % (1776)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (1756)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (1770)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (1775)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (1758)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (1769)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (1764)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (1779)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (1768)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (1766)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (1760)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (1772)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (1778)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.56  % (1772)Refutation not found, incomplete strategy% (1772)------------------------------
% 0.22/0.56  % (1772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (1772)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (1772)Memory used [KB]: 10618
% 0.22/0.56  % (1772)Time elapsed: 0.128 s
% 0.22/0.56  % (1772)------------------------------
% 0.22/0.56  % (1772)------------------------------
% 0.22/0.56  % (1762)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (1760)Refutation not found, incomplete strategy% (1760)------------------------------
% 0.22/0.56  % (1760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (1760)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (1760)Memory used [KB]: 10618
% 0.22/0.56  % (1760)Time elapsed: 0.123 s
% 0.22/0.56  % (1760)------------------------------
% 0.22/0.56  % (1760)------------------------------
% 0.22/0.56  % (1761)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.57  % (1775)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f629,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f53,f58,f63,f74,f79,f93,f102,f118,f150,f338,f395,f628])).
% 0.22/0.57  fof(f628,plain,(
% 0.22/0.57    spl5_4 | ~spl5_8 | ~spl5_12 | spl5_23),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f627])).
% 0.22/0.57  fof(f627,plain,(
% 0.22/0.57    $false | (spl5_4 | ~spl5_8 | ~spl5_12 | spl5_23)),
% 0.22/0.57    inference(subsumption_resolution,[],[f626,f393])).
% 0.22/0.57  fof(f393,plain,(
% 0.22/0.57    ~r2_hidden(sK3(sK0,sK1),k1_xboole_0) | spl5_23),
% 0.22/0.57    inference(avatar_component_clause,[],[f391])).
% 0.22/0.57  fof(f391,plain,(
% 0.22/0.57    spl5_23 <=> r2_hidden(sK3(sK0,sK1),k1_xboole_0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.22/0.57  fof(f626,plain,(
% 0.22/0.57    r2_hidden(sK3(sK0,sK1),k1_xboole_0) | (spl5_4 | ~spl5_8 | ~spl5_12)),
% 0.22/0.57    inference(forward_demodulation,[],[f625,f100])).
% 0.22/0.57  fof(f100,plain,(
% 0.22/0.57    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_8),
% 0.22/0.57    inference(avatar_component_clause,[],[f98])).
% 0.22/0.57  fof(f98,plain,(
% 0.22/0.57    spl5_8 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.57  fof(f625,plain,(
% 0.22/0.57    r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | (spl5_4 | ~spl5_12)),
% 0.22/0.57    inference(forward_demodulation,[],[f624,f30])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.57  fof(f624,plain,(
% 0.22/0.57    r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))) | (spl5_4 | ~spl5_12)),
% 0.22/0.57    inference(forward_demodulation,[],[f585,f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.57  fof(f585,plain,(
% 0.22/0.57    r2_hidden(sK3(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) | (spl5_4 | ~spl5_12)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f73,f175,f46])).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.22/0.57    inference(equality_resolution,[],[f41])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(rectify,[],[f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(flattening,[],[f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(nnf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.57  fof(f175,plain,(
% 0.22/0.57    r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK0,sK2)) | ~spl5_12),
% 0.22/0.57    inference(avatar_component_clause,[],[f173])).
% 0.22/0.57  fof(f173,plain,(
% 0.22/0.57    spl5_12 <=> r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    ~r2_hidden(sK3(sK0,sK1),sK1) | spl5_4),
% 0.22/0.57    inference(avatar_component_clause,[],[f71])).
% 0.22/0.57  fof(f71,plain,(
% 0.22/0.57    spl5_4 <=> r2_hidden(sK3(sK0,sK1),sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.57  fof(f395,plain,(
% 0.22/0.57    ~spl5_23 | ~spl5_8 | ~spl5_9),
% 0.22/0.57    inference(avatar_split_clause,[],[f381,f115,f98,f391])).
% 0.22/0.57  fof(f115,plain,(
% 0.22/0.57    spl5_9 <=> r2_hidden(sK3(sK0,sK1),k2_xboole_0(sK1,sK2))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.57  fof(f381,plain,(
% 0.22/0.57    ~r2_hidden(sK3(sK0,sK1),k1_xboole_0) | (~spl5_8 | ~spl5_9)),
% 0.22/0.57    inference(resolution,[],[f162,f117])).
% 0.22/0.57  fof(f117,plain,(
% 0.22/0.57    r2_hidden(sK3(sK0,sK1),k2_xboole_0(sK1,sK2)) | ~spl5_9),
% 0.22/0.57    inference(avatar_component_clause,[],[f115])).
% 0.22/0.57  fof(f162,plain,(
% 0.22/0.57    ( ! [X5] : (~r2_hidden(X5,k2_xboole_0(sK1,sK2)) | ~r2_hidden(X5,k1_xboole_0)) ) | ~spl5_8),
% 0.22/0.57    inference(superposition,[],[f47,f100])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(equality_resolution,[],[f40])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f26])).
% 0.22/0.57  fof(f338,plain,(
% 0.22/0.57    spl5_12 | ~spl5_5 | ~spl5_11),
% 0.22/0.57    inference(avatar_split_clause,[],[f333,f147,f76,f173])).
% 0.22/0.57  fof(f76,plain,(
% 0.22/0.57    spl5_5 <=> r2_hidden(sK3(sK0,sK1),sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.57  fof(f147,plain,(
% 0.22/0.57    spl5_11 <=> r1_tarski(sK0,k4_xboole_0(sK0,sK2))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.57  fof(f333,plain,(
% 0.22/0.57    r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK0,sK2)) | (~spl5_5 | ~spl5_11)),
% 0.22/0.57    inference(resolution,[],[f113,f149])).
% 0.22/0.57  fof(f149,plain,(
% 0.22/0.57    r1_tarski(sK0,k4_xboole_0(sK0,sK2)) | ~spl5_11),
% 0.22/0.57    inference(avatar_component_clause,[],[f147])).
% 0.22/0.57  fof(f113,plain,(
% 0.22/0.57    ( ! [X2] : (~r1_tarski(sK0,X2) | r2_hidden(sK3(sK0,sK1),X2)) ) | ~spl5_5),
% 0.22/0.57    inference(resolution,[],[f78,f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.57    inference(rectify,[],[f17])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.57    inference(nnf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,plain,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.57  fof(f78,plain,(
% 0.22/0.57    r2_hidden(sK3(sK0,sK1),sK0) | ~spl5_5),
% 0.22/0.57    inference(avatar_component_clause,[],[f76])).
% 0.22/0.57  fof(f150,plain,(
% 0.22/0.57    spl5_11 | ~spl5_7),
% 0.22/0.57    inference(avatar_split_clause,[],[f129,f89,f147])).
% 0.22/0.57  fof(f89,plain,(
% 0.22/0.57    spl5_7 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.57  fof(f129,plain,(
% 0.22/0.57    r1_tarski(sK0,k4_xboole_0(sK0,sK2)) | ~spl5_7),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f91,f36])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.57    inference(nnf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.57  fof(f91,plain,(
% 0.22/0.57    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl5_7),
% 0.22/0.57    inference(avatar_component_clause,[],[f89])).
% 0.22/0.57  fof(f118,plain,(
% 0.22/0.57    spl5_9 | ~spl5_3 | ~spl5_5),
% 0.22/0.57    inference(avatar_split_clause,[],[f109,f76,f60,f115])).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    spl5_3 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.57  fof(f109,plain,(
% 0.22/0.57    r2_hidden(sK3(sK0,sK1),k2_xboole_0(sK1,sK2)) | (~spl5_3 | ~spl5_5)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f62,f78,f33])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f60])).
% 0.22/0.57  fof(f102,plain,(
% 0.22/0.57    spl5_8 | ~spl5_3),
% 0.22/0.57    inference(avatar_split_clause,[],[f95,f60,f98])).
% 0.22/0.57  fof(f95,plain,(
% 0.22/0.57    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_3),
% 0.22/0.57    inference(resolution,[],[f62,f37])).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f21])).
% 0.22/0.57  fof(f93,plain,(
% 0.22/0.57    spl5_7 | ~spl5_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f87,f55,f89])).
% 0.22/0.57  fof(f55,plain,(
% 0.22/0.57    spl5_2 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.57  fof(f87,plain,(
% 0.22/0.57    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl5_2),
% 0.22/0.57    inference(resolution,[],[f57,f45])).
% 0.22/0.57  fof(f45,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f32,f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,plain,(
% 0.22/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,plain,(
% 0.22/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.57    inference(unused_predicate_definition_removal,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.57  fof(f57,plain,(
% 0.22/0.57    r1_xboole_0(sK0,sK2) | ~spl5_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f55])).
% 0.22/0.57  fof(f79,plain,(
% 0.22/0.57    spl5_5 | spl5_1),
% 0.22/0.57    inference(avatar_split_clause,[],[f65,f50,f76])).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    spl5_1 <=> r1_tarski(sK0,sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.57  fof(f65,plain,(
% 0.22/0.57    r2_hidden(sK3(sK0,sK1),sK0) | spl5_1),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f52,f34])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f20])).
% 0.22/0.57  fof(f52,plain,(
% 0.22/0.57    ~r1_tarski(sK0,sK1) | spl5_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f50])).
% 0.22/0.57  fof(f74,plain,(
% 0.22/0.57    ~spl5_4 | spl5_1),
% 0.22/0.57    inference(avatar_split_clause,[],[f66,f50,f71])).
% 0.22/0.57  fof(f66,plain,(
% 0.22/0.57    ~r2_hidden(sK3(sK0,sK1),sK1) | spl5_1),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f52,f35])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f20])).
% 0.22/0.57  fof(f63,plain,(
% 0.22/0.57    spl5_3),
% 0.22/0.57    inference(avatar_split_clause,[],[f27,f60])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f12,plain,(
% 0.22/0.57    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.57    inference(flattening,[],[f11])).
% 0.22/0.57  fof(f11,plain,(
% 0.22/0.57    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.57    inference(ennf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.22/0.57    inference(negated_conjecture,[],[f8])).
% 0.22/0.57  fof(f8,conjecture,(
% 0.22/0.57    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.22/0.57  fof(f58,plain,(
% 0.22/0.57    spl5_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f28,f55])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    r1_xboole_0(sK0,sK2)),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    ~spl5_1),
% 0.22/0.57    inference(avatar_split_clause,[],[f29,f50])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ~r1_tarski(sK0,sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (1775)------------------------------
% 0.22/0.57  % (1775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (1775)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (1775)Memory used [KB]: 6524
% 0.22/0.57  % (1775)Time elapsed: 0.160 s
% 0.22/0.57  % (1775)------------------------------
% 0.22/0.57  % (1775)------------------------------
% 0.22/0.58  % (1748)Success in time 0.209 s
%------------------------------------------------------------------------------
