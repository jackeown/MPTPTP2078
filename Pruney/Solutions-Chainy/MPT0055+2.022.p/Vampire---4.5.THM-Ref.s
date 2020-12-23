%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:07 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
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
fof(f388,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f222,f223,f224,f358,f360,f385,f387])).

fof(f387,plain,
    ( ~ spl6_9
    | spl6_7 ),
    inference(avatar_split_clause,[],[f386,f106,f118])).

fof(f118,plain,
    ( spl6_9
  <=> r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f106,plain,
    ( spl6_7
  <=> r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f386,plain,
    ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl6_7 ),
    inference(subsumption_resolution,[],[f114,f107])).

fof(f107,plain,
    ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f114,plain,
    ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X1] :
      ( k3_xboole_0(sK0,sK1) != X1
      | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1))
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X1),X1) ) ),
    inference(superposition,[],[f37,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

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

fof(f37,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f24])).

fof(f24,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f385,plain,
    ( spl6_9
    | spl6_7
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f381,f110,f106,f118])).

fof(f110,plain,
    ( spl6_8
  <=> r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f381,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl6_7
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f375,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f375,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | spl6_7
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f112,f107,f63])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f112,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f360,plain,
    ( ~ spl6_7
    | ~ spl6_8
    | spl6_9 ),
    inference(avatar_split_clause,[],[f359,f118,f110,f106])).

fof(f359,plain,
    ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | spl6_9 ),
    inference(subsumption_resolution,[],[f115,f119])).

fof(f119,plain,
    ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f115,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2] :
      ( k3_xboole_0(sK0,sK1) != X2
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X2),k4_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X2),sK0)
      | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X2),X2) ) ),
    inference(superposition,[],[f37,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f358,plain,(
    ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f42,f158])).

fof(f158,plain,
    ( ! [X6] : ~ r1_tarski(X6,k3_xboole_0(sK0,sK1))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl6_10
  <=> ! [X6] : ~ r1_tarski(X6,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f224,plain,
    ( spl6_10
    | ~ spl6_13
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f199,f106,f183,f157])).

fof(f183,plain,
    ( spl6_13
  <=> r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f199,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0)
        | ~ r1_tarski(X6,k3_xboole_0(sK0,sK1)) )
    | ~ spl6_7 ),
    inference(superposition,[],[f133,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f38])).

fof(f38,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f133,plain,
    ( ! [X0] : ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1)))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f108,f64])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f108,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f223,plain,
    ( ~ spl6_9
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f195,f106,f118])).

fof(f195,plain,
    ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl6_7 ),
    inference(superposition,[],[f133,f45])).

fof(f222,plain,
    ( ~ spl6_7
    | spl6_8
    | spl6_13 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | ~ spl6_7
    | spl6_8
    | spl6_13 ),
    inference(subsumption_resolution,[],[f220,f42])).

fof(f220,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ spl6_7
    | spl6_8
    | spl6_13 ),
    inference(subsumption_resolution,[],[f219,f185])).

fof(f185,plain,
    ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f183])).

fof(f219,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0)
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ spl6_7
    | spl6_8 ),
    inference(superposition,[],[f134,f62])).

fof(f134,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0))
    | ~ spl6_7
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f111,f108,f63])).

fof(f111,plain,
    ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f113,plain,
    ( spl6_7
    | spl6_8 ),
    inference(avatar_split_clause,[],[f104,f110,f106])).

fof(f104,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( k3_xboole_0(sK0,sK1) != X0
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X0),sK0)
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f37,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:05:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (32617)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (32625)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (32619)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (32619)Refutation not found, incomplete strategy% (32619)------------------------------
% 0.22/0.54  % (32619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (32625)Refutation not found, incomplete strategy% (32625)------------------------------
% 0.22/0.54  % (32625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (32625)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (32625)Memory used [KB]: 10618
% 0.22/0.54  % (32625)Time elapsed: 0.112 s
% 0.22/0.54  % (32625)------------------------------
% 0.22/0.54  % (32625)------------------------------
% 0.22/0.54  % (32627)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (32619)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (32619)Memory used [KB]: 10618
% 0.22/0.54  % (32619)Time elapsed: 0.114 s
% 0.22/0.54  % (32619)------------------------------
% 0.22/0.54  % (32619)------------------------------
% 0.22/0.55  % (32617)Refutation not found, incomplete strategy% (32617)------------------------------
% 0.22/0.55  % (32617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32617)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32617)Memory used [KB]: 1663
% 0.22/0.55  % (32617)Time elapsed: 0.124 s
% 0.22/0.55  % (32617)------------------------------
% 0.22/0.55  % (32617)------------------------------
% 0.22/0.55  % (32634)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (32634)Refutation not found, incomplete strategy% (32634)------------------------------
% 0.22/0.55  % (32634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32634)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32634)Memory used [KB]: 10618
% 0.22/0.55  % (32634)Time elapsed: 0.125 s
% 0.22/0.55  % (32634)------------------------------
% 0.22/0.55  % (32634)------------------------------
% 0.22/0.55  % (32627)Refutation not found, incomplete strategy% (32627)------------------------------
% 0.22/0.55  % (32627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32627)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32627)Memory used [KB]: 10618
% 0.22/0.55  % (32627)Time elapsed: 0.125 s
% 0.22/0.55  % (32627)------------------------------
% 0.22/0.55  % (32627)------------------------------
% 0.22/0.56  % (32639)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (32639)Refutation not found, incomplete strategy% (32639)------------------------------
% 0.22/0.56  % (32639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (32639)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (32639)Memory used [KB]: 10618
% 0.22/0.56  % (32639)Time elapsed: 0.131 s
% 0.22/0.56  % (32639)------------------------------
% 0.22/0.56  % (32639)------------------------------
% 0.22/0.56  % (32620)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.39/0.57  % (32623)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.39/0.58  % (32632)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.39/0.58  % (32632)Refutation not found, incomplete strategy% (32632)------------------------------
% 1.39/0.58  % (32632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.58  % (32632)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.58  
% 1.39/0.58  % (32632)Memory used [KB]: 6140
% 1.39/0.58  % (32632)Time elapsed: 0.003 s
% 1.39/0.58  % (32632)------------------------------
% 1.39/0.58  % (32632)------------------------------
% 1.39/0.58  % (32638)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.39/0.58  % (32624)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.39/0.59  % (32622)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.70/0.59  % (32631)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.70/0.59  % (32621)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.70/0.59  % (32621)Refutation not found, incomplete strategy% (32621)------------------------------
% 1.70/0.59  % (32621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.59  % (32621)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.59  
% 1.70/0.59  % (32621)Memory used [KB]: 6140
% 1.70/0.59  % (32621)Time elapsed: 0.161 s
% 1.70/0.59  % (32621)------------------------------
% 1.70/0.59  % (32621)------------------------------
% 1.70/0.59  % (32640)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.70/0.59  % (32626)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.70/0.59  % (32646)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.70/0.60  % (32636)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.70/0.60  % (32637)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.70/0.60  % (32618)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.70/0.60  % (32635)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.70/0.60  % (32629)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.70/0.60  % (32638)Refutation not found, incomplete strategy% (32638)------------------------------
% 1.70/0.60  % (32638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.60  % (32638)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.60  
% 1.70/0.60  % (32638)Memory used [KB]: 1663
% 1.70/0.60  % (32638)Time elapsed: 0.176 s
% 1.70/0.60  % (32638)------------------------------
% 1.70/0.60  % (32638)------------------------------
% 1.70/0.61  % (32628)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.70/0.61  % (32644)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.70/0.61  % (32628)Refutation not found, incomplete strategy% (32628)------------------------------
% 1.70/0.61  % (32628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.61  % (32628)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.61  
% 1.70/0.61  % (32628)Memory used [KB]: 10618
% 1.70/0.61  % (32628)Time elapsed: 0.184 s
% 1.70/0.61  % (32628)------------------------------
% 1.70/0.61  % (32628)------------------------------
% 1.70/0.61  % (32626)Refutation not found, incomplete strategy% (32626)------------------------------
% 1.70/0.61  % (32626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.61  % (32626)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.61  
% 1.70/0.61  % (32626)Memory used [KB]: 10618
% 1.70/0.61  % (32626)Time elapsed: 0.180 s
% 1.70/0.61  % (32626)------------------------------
% 1.70/0.61  % (32626)------------------------------
% 1.70/0.61  % (32633)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.70/0.62  % (32645)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.70/0.62  % (32637)Refutation not found, incomplete strategy% (32637)------------------------------
% 1.70/0.62  % (32637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.62  % (32637)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.62  
% 1.70/0.62  % (32637)Memory used [KB]: 10618
% 1.70/0.62  % (32637)Time elapsed: 0.194 s
% 1.70/0.62  % (32637)------------------------------
% 1.70/0.62  % (32637)------------------------------
% 1.70/0.62  % (32630)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.70/0.63  % (32643)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.70/0.63  % (32641)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.70/0.64  % (32642)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.70/0.64  % (32642)Refutation not found, incomplete strategy% (32642)------------------------------
% 1.70/0.64  % (32642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.64  % (32642)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.64  
% 1.70/0.64  % (32642)Memory used [KB]: 6140
% 1.70/0.64  % (32642)Time elapsed: 0.214 s
% 1.70/0.64  % (32642)------------------------------
% 1.70/0.64  % (32642)------------------------------
% 1.70/0.66  % (32685)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.13/0.68  % (32688)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.13/0.68  % (32643)Refutation found. Thanks to Tanya!
% 2.13/0.68  % SZS status Theorem for theBenchmark
% 2.13/0.68  % SZS output start Proof for theBenchmark
% 2.13/0.68  fof(f388,plain,(
% 2.13/0.68    $false),
% 2.13/0.68    inference(avatar_sat_refutation,[],[f113,f222,f223,f224,f358,f360,f385,f387])).
% 2.13/0.68  fof(f387,plain,(
% 2.13/0.68    ~spl6_9 | spl6_7),
% 2.13/0.68    inference(avatar_split_clause,[],[f386,f106,f118])).
% 2.13/0.68  fof(f118,plain,(
% 2.13/0.68    spl6_9 <=> r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 2.13/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 2.13/0.68  fof(f106,plain,(
% 2.13/0.68    spl6_7 <=> r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.13/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.13/0.68  fof(f386,plain,(
% 2.13/0.68    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | spl6_7),
% 2.13/0.68    inference(subsumption_resolution,[],[f114,f107])).
% 2.13/0.68  fof(f107,plain,(
% 2.13/0.68    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | spl6_7),
% 2.13/0.68    inference(avatar_component_clause,[],[f106])).
% 2.13/0.68  fof(f114,plain,(
% 2.13/0.68    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.13/0.68    inference(equality_resolution,[],[f71])).
% 2.13/0.68  fof(f71,plain,(
% 2.13/0.68    ( ! [X1] : (k3_xboole_0(sK0,sK1) != X1 | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1)) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X1),X1)) )),
% 2.13/0.68    inference(superposition,[],[f37,f57])).
% 2.13/0.68  fof(f57,plain,(
% 2.13/0.68    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 2.13/0.68    inference(cnf_transformation,[],[f36])).
% 2.13/0.68  fof(f36,plain,(
% 2.13/0.68    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.13/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).
% 2.13/0.68  fof(f35,plain,(
% 2.13/0.68    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 2.13/0.68    introduced(choice_axiom,[])).
% 2.13/0.68  fof(f34,plain,(
% 2.13/0.68    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.13/0.68    inference(rectify,[],[f33])).
% 2.13/0.68  fof(f33,plain,(
% 2.13/0.68    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.13/0.68    inference(flattening,[],[f32])).
% 2.13/0.68  fof(f32,plain,(
% 2.13/0.68    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.13/0.68    inference(nnf_transformation,[],[f3])).
% 2.13/0.68  fof(f3,axiom,(
% 2.13/0.68    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.13/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.13/0.68  fof(f37,plain,(
% 2.13/0.68    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.13/0.68    inference(cnf_transformation,[],[f25])).
% 2.13/0.68  fof(f25,plain,(
% 2.13/0.68    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.13/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f24])).
% 2.13/0.68  fof(f24,plain,(
% 2.13/0.68    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.13/0.68    introduced(choice_axiom,[])).
% 2.13/0.68  fof(f19,plain,(
% 2.13/0.68    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.13/0.68    inference(ennf_transformation,[],[f15])).
% 2.13/0.68  fof(f15,negated_conjecture,(
% 2.13/0.68    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.13/0.68    inference(negated_conjecture,[],[f14])).
% 2.13/0.68  fof(f14,conjecture,(
% 2.13/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.13/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.13/0.68  fof(f385,plain,(
% 2.13/0.68    spl6_9 | spl6_7 | ~spl6_8),
% 2.13/0.68    inference(avatar_split_clause,[],[f381,f110,f106,f118])).
% 2.13/0.68  fof(f110,plain,(
% 2.13/0.68    spl6_8 <=> r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 2.13/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.13/0.68  fof(f381,plain,(
% 2.13/0.68    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | (spl6_7 | ~spl6_8)),
% 2.13/0.68    inference(forward_demodulation,[],[f375,f45])).
% 2.13/0.68  fof(f45,plain,(
% 2.13/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.13/0.68    inference(cnf_transformation,[],[f13])).
% 2.13/0.68  fof(f13,axiom,(
% 2.13/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.13/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.13/0.68  fof(f375,plain,(
% 2.13/0.68    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))) | (spl6_7 | ~spl6_8)),
% 2.13/0.68    inference(unit_resulting_resolution,[],[f112,f107,f63])).
% 2.13/0.68  fof(f63,plain,(
% 2.13/0.68    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.13/0.68    inference(equality_resolution,[],[f55])).
% 2.13/0.68  fof(f55,plain,(
% 2.13/0.68    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.13/0.68    inference(cnf_transformation,[],[f36])).
% 2.13/0.68  fof(f112,plain,(
% 2.13/0.68    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~spl6_8),
% 2.13/0.68    inference(avatar_component_clause,[],[f110])).
% 2.13/0.68  fof(f360,plain,(
% 2.13/0.68    ~spl6_7 | ~spl6_8 | spl6_9),
% 2.13/0.68    inference(avatar_split_clause,[],[f359,f118,f110,f106])).
% 2.13/0.68  fof(f359,plain,(
% 2.13/0.68    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | spl6_9),
% 2.13/0.68    inference(subsumption_resolution,[],[f115,f119])).
% 2.13/0.68  fof(f119,plain,(
% 2.13/0.68    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | spl6_9),
% 2.13/0.68    inference(avatar_component_clause,[],[f118])).
% 2.13/0.68  fof(f115,plain,(
% 2.13/0.68    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.13/0.68    inference(equality_resolution,[],[f72])).
% 2.13/0.68  fof(f72,plain,(
% 2.13/0.68    ( ! [X2] : (k3_xboole_0(sK0,sK1) != X2 | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X2),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X2),sK0) | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X2),X2)) )),
% 2.13/0.68    inference(superposition,[],[f37,f58])).
% 2.13/0.68  fof(f58,plain,(
% 2.13/0.68    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) )),
% 2.13/0.68    inference(cnf_transformation,[],[f36])).
% 2.13/0.68  fof(f358,plain,(
% 2.13/0.68    ~spl6_10),
% 2.13/0.68    inference(avatar_contradiction_clause,[],[f357])).
% 2.13/0.68  fof(f357,plain,(
% 2.13/0.68    $false | ~spl6_10),
% 2.13/0.68    inference(unit_resulting_resolution,[],[f42,f158])).
% 2.13/0.68  fof(f158,plain,(
% 2.13/0.68    ( ! [X6] : (~r1_tarski(X6,k3_xboole_0(sK0,sK1))) ) | ~spl6_10),
% 2.13/0.68    inference(avatar_component_clause,[],[f157])).
% 2.13/0.68  fof(f157,plain,(
% 2.13/0.68    spl6_10 <=> ! [X6] : ~r1_tarski(X6,k3_xboole_0(sK0,sK1))),
% 2.13/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 2.13/0.68  fof(f42,plain,(
% 2.13/0.68    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.13/0.68    inference(cnf_transformation,[],[f8])).
% 2.13/0.68  fof(f8,axiom,(
% 2.13/0.68    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.13/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.13/0.68  fof(f224,plain,(
% 2.13/0.68    spl6_10 | ~spl6_13 | ~spl6_7),
% 2.13/0.68    inference(avatar_split_clause,[],[f199,f106,f183,f157])).
% 2.13/0.68  fof(f183,plain,(
% 2.13/0.68    spl6_13 <=> r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0)),
% 2.13/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 2.13/0.68  fof(f199,plain,(
% 2.13/0.68    ( ! [X6] : (~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0) | ~r1_tarski(X6,k3_xboole_0(sK0,sK1))) ) | ~spl6_7),
% 2.13/0.68    inference(superposition,[],[f133,f62])).
% 2.13/0.68  fof(f62,plain,(
% 2.13/0.68    ( ! [X0,X1] : (o_0_0_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.13/0.68    inference(definition_unfolding,[],[f52,f38])).
% 2.13/0.68  fof(f38,plain,(
% 2.13/0.68    k1_xboole_0 = o_0_0_xboole_0),
% 2.13/0.68    inference(cnf_transformation,[],[f2])).
% 2.13/0.68  fof(f2,axiom,(
% 2.13/0.68    k1_xboole_0 = o_0_0_xboole_0),
% 2.13/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 2.13/0.68  fof(f52,plain,(
% 2.13/0.68    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.13/0.68    inference(cnf_transformation,[],[f23])).
% 2.13/0.68  fof(f23,plain,(
% 2.13/0.68    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 2.13/0.68    inference(ennf_transformation,[],[f18])).
% 2.13/0.68  fof(f18,plain,(
% 2.13/0.68    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 2.13/0.68    inference(unused_predicate_definition_removal,[],[f7])).
% 2.13/0.68  fof(f7,axiom,(
% 2.13/0.68    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.13/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.13/0.68  fof(f133,plain,(
% 2.13/0.68    ( ! [X0] : (~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1)))) ) | ~spl6_7),
% 2.13/0.68    inference(unit_resulting_resolution,[],[f108,f64])).
% 2.13/0.68  fof(f64,plain,(
% 2.13/0.68    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.13/0.68    inference(equality_resolution,[],[f54])).
% 2.13/0.68  fof(f54,plain,(
% 2.13/0.68    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.13/0.68    inference(cnf_transformation,[],[f36])).
% 2.13/0.68  fof(f108,plain,(
% 2.13/0.68    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~spl6_7),
% 2.13/0.68    inference(avatar_component_clause,[],[f106])).
% 2.13/0.68  fof(f223,plain,(
% 2.13/0.68    ~spl6_9 | ~spl6_7),
% 2.13/0.68    inference(avatar_split_clause,[],[f195,f106,f118])).
% 2.13/0.68  fof(f195,plain,(
% 2.13/0.68    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl6_7),
% 2.13/0.68    inference(superposition,[],[f133,f45])).
% 2.13/0.68  fof(f222,plain,(
% 2.13/0.68    ~spl6_7 | spl6_8 | spl6_13),
% 2.13/0.68    inference(avatar_contradiction_clause,[],[f221])).
% 2.13/0.68  fof(f221,plain,(
% 2.13/0.68    $false | (~spl6_7 | spl6_8 | spl6_13)),
% 2.13/0.68    inference(subsumption_resolution,[],[f220,f42])).
% 2.13/0.68  fof(f220,plain,(
% 2.13/0.68    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | (~spl6_7 | spl6_8 | spl6_13)),
% 2.13/0.68    inference(subsumption_resolution,[],[f219,f185])).
% 2.13/0.68  fof(f185,plain,(
% 2.13/0.68    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0) | spl6_13),
% 2.13/0.68    inference(avatar_component_clause,[],[f183])).
% 2.13/0.68  fof(f219,plain,(
% 2.13/0.68    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | (~spl6_7 | spl6_8)),
% 2.13/0.68    inference(superposition,[],[f134,f62])).
% 2.13/0.68  fof(f134,plain,(
% 2.13/0.68    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0)) | (~spl6_7 | spl6_8)),
% 2.13/0.68    inference(unit_resulting_resolution,[],[f111,f108,f63])).
% 2.13/0.68  fof(f111,plain,(
% 2.13/0.68    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | spl6_8),
% 2.13/0.68    inference(avatar_component_clause,[],[f110])).
% 2.13/0.68  fof(f113,plain,(
% 2.13/0.68    spl6_7 | spl6_8),
% 2.13/0.68    inference(avatar_split_clause,[],[f104,f110,f106])).
% 2.13/0.68  fof(f104,plain,(
% 2.13/0.68    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.13/0.68    inference(equality_resolution,[],[f70])).
% 2.13/0.68  fof(f70,plain,(
% 2.13/0.68    ( ! [X0] : (k3_xboole_0(sK0,sK1) != X0 | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X0),sK0) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X0),X0)) )),
% 2.13/0.68    inference(superposition,[],[f37,f56])).
% 2.13/0.68  fof(f56,plain,(
% 2.13/0.68    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 2.13/0.68    inference(cnf_transformation,[],[f36])).
% 2.13/0.68  % SZS output end Proof for theBenchmark
% 2.13/0.68  % (32643)------------------------------
% 2.13/0.68  % (32643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.68  % (32643)Termination reason: Refutation
% 2.13/0.68  
% 2.13/0.68  % (32643)Memory used [KB]: 10874
% 2.13/0.68  % (32643)Time elapsed: 0.237 s
% 2.13/0.68  % (32643)------------------------------
% 2.13/0.68  % (32643)------------------------------
% 2.18/0.69  % (32616)Success in time 0.312 s
%------------------------------------------------------------------------------
