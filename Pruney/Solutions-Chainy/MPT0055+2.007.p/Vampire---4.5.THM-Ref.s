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
% DateTime   : Thu Dec  3 12:30:05 EST 2020

% Result     : Theorem 2.81s
% Output     : Refutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 422 expanded)
%              Number of leaves         :   22 ( 119 expanded)
%              Depth                    :   27
%              Number of atoms          :  355 (1933 expanded)
%              Number of equality atoms :   55 ( 221 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10240,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2840,f2964,f4773,f6729,f6817,f7395,f10238])).

fof(f10238,plain,
    ( spl6_7
    | ~ spl6_8
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f10237])).

fof(f10237,plain,
    ( $false
    | spl6_7
    | ~ spl6_8
    | spl6_9 ),
    inference(subsumption_resolution,[],[f10236,f137])).

fof(f137,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl6_9
  <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f10236,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl6_7
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f10220,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f10220,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | spl6_7
    | ~ spl6_8 ),
    inference(resolution,[],[f373,f122])).

fof(f122,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_8
  <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f373,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)
        | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1))) )
    | spl6_7 ),
    inference(resolution,[],[f117,f63])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f117,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl6_7
  <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f7395,plain,
    ( ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f7394])).

fof(f7394,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f7382,f138])).

fof(f138,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f7382,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl6_7 ),
    inference(superposition,[],[f128,f47])).

fof(f128,plain,
    ( ! [X2] : ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X2,k3_xboole_0(sK0,sK1)))
    | ~ spl6_7 ),
    inference(resolution,[],[f118,f64])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f118,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f6817,plain,
    ( ~ spl6_7
    | spl6_9
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f6816,f120,f136,f116])).

fof(f6816,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f6802,f39])).

fof(f39,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f26])).

fof(f26,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f6802,plain,
    ( k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl6_8 ),
    inference(resolution,[],[f122,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6729,plain,
    ( spl6_8
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(avatar_contradiction_clause,[],[f6728])).

fof(f6728,plain,
    ( $false
    | spl6_8
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f4752,f121])).

fof(f121,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f4752,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f4751,f3912])).

fof(f3912,plain,
    ( ! [X17,X18,X16] :
        ( ~ r2_hidden(X18,k3_xboole_0(X16,X17))
        | r2_hidden(X18,X16) )
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f3891,f2979])).

fof(f2979,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f2976,f2957])).

fof(f2957,plain,
    ( r1_xboole_0(k1_xboole_0,sK1)
    | ~ spl6_42 ),
    inference(resolution,[],[f2947,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f2947,plain,
    ( ! [X1] : ~ r2_hidden(X1,k3_xboole_0(k1_xboole_0,sK1))
    | ~ spl6_42 ),
    inference(forward_demodulation,[],[f2945,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2945,plain,
    ( ! [X1] : ~ r2_hidden(X1,k3_xboole_0(sK1,k1_xboole_0))
    | ~ spl6_42 ),
    inference(resolution,[],[f2940,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2940,plain,
    ( r1_xboole_0(sK1,k1_xboole_0)
    | ~ spl6_42 ),
    inference(duplicate_literal_removal,[],[f2935])).

fof(f2935,plain,
    ( r1_xboole_0(sK1,k1_xboole_0)
    | r1_xboole_0(sK1,k1_xboole_0)
    | ~ spl6_42 ),
    inference(resolution,[],[f2884,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
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

fof(f2884,plain,
    ( ! [X12] :
        ( ~ r2_hidden(sK5(X12,k1_xboole_0),sK1)
        | r1_xboole_0(X12,k1_xboole_0) )
    | ~ spl6_42 ),
    inference(resolution,[],[f2863,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2863,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_xboole_0)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl6_42 ),
    inference(superposition,[],[f64,f2842])).

fof(f2842,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)
    | ~ spl6_42 ),
    inference(resolution,[],[f811,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f811,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f810])).

fof(f810,plain,
    ( spl6_42
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f2976,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ r1_xboole_0(k1_xboole_0,sK1) )
    | ~ spl6_43 ),
    inference(superposition,[],[f58,f815])).

fof(f815,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f814])).

fof(f814,plain,
    ( spl6_43
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f3891,plain,
    ( ! [X17,X18,X16] :
        ( r2_hidden(X18,k1_xboole_0)
        | r2_hidden(X18,X16)
        | ~ r2_hidden(X18,k3_xboole_0(X16,X17)) )
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(superposition,[],[f63,f3813])).

fof(f3813,plain,
    ( ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X5,X6),X5)
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(superposition,[],[f3752,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f3752,plain,
    ( ! [X8,X9] : k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,X8))
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(forward_demodulation,[],[f3718,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f3718,plain,
    ( ! [X8,X9] : k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9)))
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(superposition,[],[f3710,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f3710,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(X3,X3)
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f3707,f2979])).

fof(f3707,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k4_xboole_0(X3,X3)
        | r2_hidden(sK2(X3,X3,k1_xboole_0),k1_xboole_0) )
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(duplicate_literal_removal,[],[f3691])).

fof(f3691,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k4_xboole_0(X3,X3)
        | k1_xboole_0 = k4_xboole_0(X3,X3)
        | r2_hidden(sK2(X3,X3,k1_xboole_0),k1_xboole_0) )
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(resolution,[],[f2985,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2985,plain,
    ( ! [X6,X7] :
        ( r2_hidden(sK2(X6,X7,k1_xboole_0),X6)
        | k1_xboole_0 = k4_xboole_0(X6,X7) )
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(resolution,[],[f2979,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4751,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( k3_xboole_0(sK0,sK1) != X0
      | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X0),sK0)
      | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f39,f43])).

fof(f4773,plain,
    ( spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f4772,f136,f116])).

fof(f4772,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X1] :
      ( k3_xboole_0(sK0,sK1) != X1
      | ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1))
      | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X1),X1) ) ),
    inference(superposition,[],[f39,f44])).

fof(f2964,plain,
    ( ~ spl6_42
    | spl6_43 ),
    inference(avatar_contradiction_clause,[],[f2963])).

fof(f2963,plain,
    ( $false
    | ~ spl6_42
    | spl6_43 ),
    inference(subsumption_resolution,[],[f2956,f816])).

fof(f816,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK1)
    | spl6_43 ),
    inference(avatar_component_clause,[],[f814])).

fof(f2956,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl6_42 ),
    inference(resolution,[],[f2947,f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f2840,plain,(
    spl6_42 ),
    inference(avatar_contradiction_clause,[],[f2839])).

fof(f2839,plain,
    ( $false
    | spl6_42 ),
    inference(subsumption_resolution,[],[f2828,f2766])).

fof(f2766,plain,
    ( ! [X0] : ~ r1_xboole_0(sK1,X0)
    | spl6_42 ),
    inference(resolution,[],[f2494,f58])).

fof(f2494,plain,
    ( ! [X0] : r2_hidden(sK3(k3_xboole_0(sK1,X0)),k3_xboole_0(sK1,X0))
    | spl6_42 ),
    inference(resolution,[],[f2152,f59])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f2152,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | r2_hidden(sK3(X0),X0) )
    | spl6_42 ),
    inference(superposition,[],[f812,f53])).

fof(f812,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl6_42 ),
    inference(avatar_component_clause,[],[f810])).

fof(f2828,plain,
    ( ! [X1] : r1_xboole_0(sK1,k4_xboole_0(X1,sK1))
    | spl6_42 ),
    inference(resolution,[],[f2785,f61])).

fof(f2785,plain,
    ( ! [X4,X5] : ~ r2_hidden(sK5(sK1,X4),k4_xboole_0(X5,sK1))
    | spl6_42 ),
    inference(resolution,[],[f2773,f64])).

fof(f2773,plain,
    ( ! [X0] : r2_hidden(sK5(sK1,X0),sK1)
    | spl6_42 ),
    inference(resolution,[],[f2766,f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:24:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (19309)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (19309)Refutation not found, incomplete strategy% (19309)------------------------------
% 0.20/0.47  % (19309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (19309)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (19309)Memory used [KB]: 10618
% 0.20/0.47  % (19309)Time elapsed: 0.050 s
% 0.20/0.47  % (19309)------------------------------
% 0.20/0.47  % (19309)------------------------------
% 0.20/0.48  % (19322)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (19315)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (19323)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (19323)Refutation not found, incomplete strategy% (19323)------------------------------
% 0.20/0.48  % (19323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (19323)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (19323)Memory used [KB]: 6140
% 0.20/0.48  % (19323)Time elapsed: 0.002 s
% 0.20/0.48  % (19323)------------------------------
% 0.20/0.48  % (19323)------------------------------
% 0.20/0.50  % (19314)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (19311)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (19311)Refutation not found, incomplete strategy% (19311)------------------------------
% 0.20/0.50  % (19311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (19311)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (19311)Memory used [KB]: 10618
% 0.20/0.50  % (19311)Time elapsed: 0.084 s
% 0.20/0.50  % (19311)------------------------------
% 0.20/0.50  % (19311)------------------------------
% 0.20/0.50  % (19313)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (19325)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % (19308)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (19327)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (19324)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.51  % (19308)Refutation not found, incomplete strategy% (19308)------------------------------
% 0.20/0.51  % (19308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (19308)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (19308)Memory used [KB]: 6140
% 0.20/0.51  % (19308)Time elapsed: 0.092 s
% 0.20/0.51  % (19308)------------------------------
% 0.20/0.51  % (19308)------------------------------
% 0.20/0.51  % (19328)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (19316)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.51  % (19328)Refutation not found, incomplete strategy% (19328)------------------------------
% 0.20/0.51  % (19328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (19328)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (19328)Memory used [KB]: 10490
% 0.20/0.51  % (19328)Time elapsed: 0.094 s
% 0.20/0.51  % (19328)------------------------------
% 0.20/0.51  % (19328)------------------------------
% 0.20/0.51  % (19312)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.51  % (19310)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.51  % (19321)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  % (19321)Refutation not found, incomplete strategy% (19321)------------------------------
% 0.20/0.51  % (19321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (19321)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (19321)Memory used [KB]: 1663
% 0.20/0.51  % (19321)Time elapsed: 0.108 s
% 0.20/0.51  % (19321)------------------------------
% 0.20/0.51  % (19321)------------------------------
% 0.20/0.52  % (19318)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.52  % (19320)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (19318)Refutation not found, incomplete strategy% (19318)------------------------------
% 0.20/0.52  % (19318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (19318)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (19318)Memory used [KB]: 6012
% 0.20/0.52  % (19318)Time elapsed: 0.105 s
% 0.20/0.52  % (19318)------------------------------
% 0.20/0.52  % (19318)------------------------------
% 0.20/0.52  % (19326)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.53  % (19319)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.53  % (19319)Refutation not found, incomplete strategy% (19319)------------------------------
% 0.20/0.53  % (19319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (19319)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (19319)Memory used [KB]: 10618
% 0.20/0.53  % (19319)Time elapsed: 0.115 s
% 0.20/0.53  % (19319)------------------------------
% 0.20/0.53  % (19319)------------------------------
% 0.20/0.53  % (19317)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.54  % (19320)Refutation not found, incomplete strategy% (19320)------------------------------
% 0.20/0.54  % (19320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (19320)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (19320)Memory used [KB]: 6012
% 0.20/0.54  % (19320)Time elapsed: 0.002 s
% 0.20/0.54  % (19320)------------------------------
% 0.20/0.54  % (19320)------------------------------
% 2.81/0.75  % (19327)Refutation found. Thanks to Tanya!
% 2.81/0.75  % SZS status Theorem for theBenchmark
% 2.81/0.75  % SZS output start Proof for theBenchmark
% 2.81/0.75  fof(f10240,plain,(
% 2.81/0.75    $false),
% 2.81/0.75    inference(avatar_sat_refutation,[],[f2840,f2964,f4773,f6729,f6817,f7395,f10238])).
% 2.81/0.75  fof(f10238,plain,(
% 2.81/0.75    spl6_7 | ~spl6_8 | spl6_9),
% 2.81/0.75    inference(avatar_contradiction_clause,[],[f10237])).
% 2.81/0.75  fof(f10237,plain,(
% 2.81/0.75    $false | (spl6_7 | ~spl6_8 | spl6_9)),
% 2.81/0.75    inference(subsumption_resolution,[],[f10236,f137])).
% 2.81/0.75  fof(f137,plain,(
% 2.81/0.75    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | spl6_9),
% 2.81/0.75    inference(avatar_component_clause,[],[f136])).
% 2.81/0.75  fof(f136,plain,(
% 2.81/0.75    spl6_9 <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 2.81/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 2.81/0.75  fof(f10236,plain,(
% 2.81/0.75    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | (spl6_7 | ~spl6_8)),
% 2.81/0.75    inference(forward_demodulation,[],[f10220,f47])).
% 2.81/0.75  fof(f47,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.81/0.75    inference(cnf_transformation,[],[f15])).
% 2.81/0.75  fof(f15,axiom,(
% 2.81/0.75    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.81/0.75  fof(f10220,plain,(
% 2.81/0.75    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))) | (spl6_7 | ~spl6_8)),
% 2.81/0.75    inference(resolution,[],[f373,f122])).
% 2.81/0.75  fof(f122,plain,(
% 2.81/0.75    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~spl6_8),
% 2.81/0.75    inference(avatar_component_clause,[],[f120])).
% 2.81/0.75  fof(f120,plain,(
% 2.81/0.75    spl6_8 <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 2.81/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.81/0.75  fof(f373,plain,(
% 2.81/0.75    ( ! [X1] : (~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1)))) ) | spl6_7),
% 2.81/0.75    inference(resolution,[],[f117,f63])).
% 2.81/0.75  fof(f63,plain,(
% 2.81/0.75    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.81/0.75    inference(equality_resolution,[],[f42])).
% 2.81/0.75  fof(f42,plain,(
% 2.81/0.75    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.81/0.75    inference(cnf_transformation,[],[f32])).
% 2.81/0.75  fof(f32,plain,(
% 2.81/0.75    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.81/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 2.81/0.75  fof(f31,plain,(
% 2.81/0.75    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.81/0.75    introduced(choice_axiom,[])).
% 2.81/0.75  fof(f30,plain,(
% 2.81/0.75    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.81/0.75    inference(rectify,[],[f29])).
% 2.81/0.75  fof(f29,plain,(
% 2.81/0.75    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.81/0.75    inference(flattening,[],[f28])).
% 2.81/0.75  fof(f28,plain,(
% 2.81/0.75    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.81/0.75    inference(nnf_transformation,[],[f3])).
% 2.81/0.75  fof(f3,axiom,(
% 2.81/0.75    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.81/0.75  fof(f117,plain,(
% 2.81/0.75    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | spl6_7),
% 2.81/0.75    inference(avatar_component_clause,[],[f116])).
% 2.81/0.75  fof(f116,plain,(
% 2.81/0.75    spl6_7 <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.81/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.81/0.75  fof(f7395,plain,(
% 2.81/0.75    ~spl6_7 | ~spl6_9),
% 2.81/0.75    inference(avatar_contradiction_clause,[],[f7394])).
% 2.81/0.75  fof(f7394,plain,(
% 2.81/0.75    $false | (~spl6_7 | ~spl6_9)),
% 2.81/0.75    inference(subsumption_resolution,[],[f7382,f138])).
% 2.81/0.75  fof(f138,plain,(
% 2.81/0.75    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl6_9),
% 2.81/0.75    inference(avatar_component_clause,[],[f136])).
% 2.81/0.75  fof(f7382,plain,(
% 2.81/0.75    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl6_7),
% 2.81/0.75    inference(superposition,[],[f128,f47])).
% 2.81/0.75  fof(f128,plain,(
% 2.81/0.75    ( ! [X2] : (~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X2,k3_xboole_0(sK0,sK1)))) ) | ~spl6_7),
% 2.81/0.75    inference(resolution,[],[f118,f64])).
% 2.81/0.75  fof(f64,plain,(
% 2.81/0.75    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.81/0.75    inference(equality_resolution,[],[f41])).
% 2.81/0.75  fof(f41,plain,(
% 2.81/0.75    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.81/0.75    inference(cnf_transformation,[],[f32])).
% 2.81/0.75  fof(f118,plain,(
% 2.81/0.75    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~spl6_7),
% 2.81/0.75    inference(avatar_component_clause,[],[f116])).
% 2.81/0.75  fof(f6817,plain,(
% 2.81/0.75    ~spl6_7 | spl6_9 | ~spl6_8),
% 2.81/0.75    inference(avatar_split_clause,[],[f6816,f120,f136,f116])).
% 2.81/0.75  fof(f6816,plain,(
% 2.81/0.75    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~spl6_8),
% 2.81/0.75    inference(subsumption_resolution,[],[f6802,f39])).
% 2.81/0.75  fof(f39,plain,(
% 2.81/0.75    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.81/0.75    inference(cnf_transformation,[],[f27])).
% 2.81/0.75  fof(f27,plain,(
% 2.81/0.75    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.81/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f26])).
% 2.81/0.75  fof(f26,plain,(
% 2.81/0.75    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.81/0.75    introduced(choice_axiom,[])).
% 2.81/0.75  fof(f21,plain,(
% 2.81/0.75    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.81/0.75    inference(ennf_transformation,[],[f17])).
% 2.81/0.75  fof(f17,negated_conjecture,(
% 2.81/0.75    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.81/0.75    inference(negated_conjecture,[],[f16])).
% 2.81/0.75  fof(f16,conjecture,(
% 2.81/0.75    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.81/0.75  fof(f6802,plain,(
% 2.81/0.75    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~spl6_8),
% 2.81/0.75    inference(resolution,[],[f122,f45])).
% 2.81/0.75  fof(f45,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f32])).
% 2.81/0.75  fof(f6729,plain,(
% 2.81/0.75    spl6_8 | ~spl6_42 | ~spl6_43),
% 2.81/0.75    inference(avatar_contradiction_clause,[],[f6728])).
% 2.81/0.75  fof(f6728,plain,(
% 2.81/0.75    $false | (spl6_8 | ~spl6_42 | ~spl6_43)),
% 2.81/0.75    inference(subsumption_resolution,[],[f4752,f121])).
% 2.81/0.75  fof(f121,plain,(
% 2.81/0.75    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | spl6_8),
% 2.81/0.75    inference(avatar_component_clause,[],[f120])).
% 2.81/0.75  fof(f4752,plain,(
% 2.81/0.75    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | (~spl6_42 | ~spl6_43)),
% 2.81/0.75    inference(subsumption_resolution,[],[f4751,f3912])).
% 2.81/0.75  fof(f3912,plain,(
% 2.81/0.75    ( ! [X17,X18,X16] : (~r2_hidden(X18,k3_xboole_0(X16,X17)) | r2_hidden(X18,X16)) ) | (~spl6_42 | ~spl6_43)),
% 2.81/0.75    inference(subsumption_resolution,[],[f3891,f2979])).
% 2.81/0.75  fof(f2979,plain,(
% 2.81/0.75    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl6_42 | ~spl6_43)),
% 2.81/0.75    inference(subsumption_resolution,[],[f2976,f2957])).
% 2.81/0.75  fof(f2957,plain,(
% 2.81/0.75    r1_xboole_0(k1_xboole_0,sK1) | ~spl6_42),
% 2.81/0.75    inference(resolution,[],[f2947,f57])).
% 2.81/0.75  fof(f57,plain,(
% 2.81/0.75    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f36])).
% 2.81/0.75  fof(f36,plain,(
% 2.81/0.75    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.81/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f35])).
% 2.81/0.75  fof(f35,plain,(
% 2.81/0.75    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 2.81/0.75    introduced(choice_axiom,[])).
% 2.81/0.75  fof(f24,plain,(
% 2.81/0.75    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.81/0.75    inference(ennf_transformation,[],[f18])).
% 2.81/0.75  fof(f18,plain,(
% 2.81/0.75    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.81/0.75    inference(rectify,[],[f5])).
% 2.81/0.75  fof(f5,axiom,(
% 2.81/0.75    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.81/0.75  fof(f2947,plain,(
% 2.81/0.75    ( ! [X1] : (~r2_hidden(X1,k3_xboole_0(k1_xboole_0,sK1))) ) | ~spl6_42),
% 2.81/0.75    inference(forward_demodulation,[],[f2945,f50])).
% 2.81/0.75  fof(f50,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f2])).
% 2.81/0.75  fof(f2,axiom,(
% 2.81/0.75    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.81/0.75  fof(f2945,plain,(
% 2.81/0.75    ( ! [X1] : (~r2_hidden(X1,k3_xboole_0(sK1,k1_xboole_0))) ) | ~spl6_42),
% 2.81/0.75    inference(resolution,[],[f2940,f58])).
% 2.81/0.75  fof(f58,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.81/0.75    inference(cnf_transformation,[],[f36])).
% 2.81/0.75  fof(f2940,plain,(
% 2.81/0.75    r1_xboole_0(sK1,k1_xboole_0) | ~spl6_42),
% 2.81/0.75    inference(duplicate_literal_removal,[],[f2935])).
% 2.81/0.75  fof(f2935,plain,(
% 2.81/0.75    r1_xboole_0(sK1,k1_xboole_0) | r1_xboole_0(sK1,k1_xboole_0) | ~spl6_42),
% 2.81/0.75    inference(resolution,[],[f2884,f60])).
% 2.81/0.75  fof(f60,plain,(
% 2.81/0.75    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f38])).
% 2.81/0.75  fof(f38,plain,(
% 2.81/0.75    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.81/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f37])).
% 2.81/0.75  fof(f37,plain,(
% 2.81/0.75    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 2.81/0.75    introduced(choice_axiom,[])).
% 2.81/0.75  fof(f25,plain,(
% 2.81/0.75    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.81/0.75    inference(ennf_transformation,[],[f19])).
% 2.81/0.75  fof(f19,plain,(
% 2.81/0.75    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.81/0.75    inference(rectify,[],[f4])).
% 2.81/0.75  fof(f4,axiom,(
% 2.81/0.75    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.81/0.75  fof(f2884,plain,(
% 2.81/0.75    ( ! [X12] : (~r2_hidden(sK5(X12,k1_xboole_0),sK1) | r1_xboole_0(X12,k1_xboole_0)) ) | ~spl6_42),
% 2.81/0.75    inference(resolution,[],[f2863,f61])).
% 2.81/0.75  fof(f61,plain,(
% 2.81/0.75    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f38])).
% 2.81/0.75  fof(f2863,plain,(
% 2.81/0.75    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0) | ~r2_hidden(X5,sK1)) ) | ~spl6_42),
% 2.81/0.75    inference(superposition,[],[f64,f2842])).
% 2.81/0.75  fof(f2842,plain,(
% 2.81/0.75    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) | ~spl6_42),
% 2.81/0.75    inference(resolution,[],[f811,f56])).
% 2.81/0.75  fof(f56,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f23])).
% 2.81/0.75  fof(f23,plain,(
% 2.81/0.75    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 2.81/0.75    inference(ennf_transformation,[],[f20])).
% 2.81/0.75  fof(f20,plain,(
% 2.81/0.75    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 2.81/0.75    inference(unused_predicate_definition_removal,[],[f7])).
% 2.81/0.75  fof(f7,axiom,(
% 2.81/0.75    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.81/0.75  fof(f811,plain,(
% 2.81/0.75    r1_tarski(k1_xboole_0,sK1) | ~spl6_42),
% 2.81/0.75    inference(avatar_component_clause,[],[f810])).
% 2.81/0.75  fof(f810,plain,(
% 2.81/0.75    spl6_42 <=> r1_tarski(k1_xboole_0,sK1)),
% 2.81/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 2.81/0.75  fof(f2976,plain,(
% 2.81/0.75    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,sK1)) ) | ~spl6_43),
% 2.81/0.75    inference(superposition,[],[f58,f815])).
% 2.81/0.75  fof(f815,plain,(
% 2.81/0.75    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) | ~spl6_43),
% 2.81/0.75    inference(avatar_component_clause,[],[f814])).
% 2.81/0.75  fof(f814,plain,(
% 2.81/0.75    spl6_43 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)),
% 2.81/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 2.81/0.75  fof(f3891,plain,(
% 2.81/0.75    ( ! [X17,X18,X16] : (r2_hidden(X18,k1_xboole_0) | r2_hidden(X18,X16) | ~r2_hidden(X18,k3_xboole_0(X16,X17))) ) | (~spl6_42 | ~spl6_43)),
% 2.81/0.75    inference(superposition,[],[f63,f3813])).
% 2.81/0.75  fof(f3813,plain,(
% 2.81/0.75    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X5,X6),X5)) ) | (~spl6_42 | ~spl6_43)),
% 2.81/0.75    inference(superposition,[],[f3752,f49])).
% 2.81/0.75  fof(f49,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.81/0.75    inference(cnf_transformation,[],[f10])).
% 2.81/0.75  fof(f10,axiom,(
% 2.81/0.75    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 2.81/0.75  fof(f3752,plain,(
% 2.81/0.75    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,X8))) ) | (~spl6_42 | ~spl6_43)),
% 2.81/0.75    inference(forward_demodulation,[],[f3718,f48])).
% 2.81/0.75  fof(f48,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.81/0.75    inference(cnf_transformation,[],[f11])).
% 2.81/0.75  fof(f11,axiom,(
% 2.81/0.75    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.81/0.75  fof(f3718,plain,(
% 2.81/0.75    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9)))) ) | (~spl6_42 | ~spl6_43)),
% 2.81/0.75    inference(superposition,[],[f3710,f46])).
% 2.81/0.75  fof(f46,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.81/0.75    inference(cnf_transformation,[],[f13])).
% 2.81/0.75  fof(f13,axiom,(
% 2.81/0.75    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.81/0.75  fof(f3710,plain,(
% 2.81/0.75    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3)) ) | (~spl6_42 | ~spl6_43)),
% 2.81/0.75    inference(subsumption_resolution,[],[f3707,f2979])).
% 2.81/0.75  fof(f3707,plain,(
% 2.81/0.75    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3) | r2_hidden(sK2(X3,X3,k1_xboole_0),k1_xboole_0)) ) | (~spl6_42 | ~spl6_43)),
% 2.81/0.75    inference(duplicate_literal_removal,[],[f3691])).
% 2.81/0.75  fof(f3691,plain,(
% 2.81/0.75    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3) | k1_xboole_0 = k4_xboole_0(X3,X3) | r2_hidden(sK2(X3,X3,k1_xboole_0),k1_xboole_0)) ) | (~spl6_42 | ~spl6_43)),
% 2.81/0.75    inference(resolution,[],[f2985,f44])).
% 2.81/0.75  fof(f44,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f32])).
% 2.81/0.75  fof(f2985,plain,(
% 2.81/0.75    ( ! [X6,X7] : (r2_hidden(sK2(X6,X7,k1_xboole_0),X6) | k1_xboole_0 = k4_xboole_0(X6,X7)) ) | (~spl6_42 | ~spl6_43)),
% 2.81/0.75    inference(resolution,[],[f2979,f43])).
% 2.81/0.75  fof(f43,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f32])).
% 2.81/0.75  fof(f4751,plain,(
% 2.81/0.75    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.81/0.75    inference(equality_resolution,[],[f71])).
% 2.81/0.75  fof(f71,plain,(
% 2.81/0.75    ( ! [X0] : (k3_xboole_0(sK0,sK1) != X0 | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X0),sK0) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X0),X0)) )),
% 2.81/0.75    inference(superposition,[],[f39,f43])).
% 2.81/0.75  fof(f4773,plain,(
% 2.81/0.75    spl6_7 | ~spl6_9),
% 2.81/0.75    inference(avatar_split_clause,[],[f4772,f136,f116])).
% 2.81/0.75  fof(f4772,plain,(
% 2.81/0.75    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.81/0.75    inference(equality_resolution,[],[f72])).
% 2.81/0.75  fof(f72,plain,(
% 2.81/0.75    ( ! [X1] : (k3_xboole_0(sK0,sK1) != X1 | ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1)) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X1),X1)) )),
% 2.81/0.75    inference(superposition,[],[f39,f44])).
% 2.81/0.75  fof(f2964,plain,(
% 2.81/0.75    ~spl6_42 | spl6_43),
% 2.81/0.75    inference(avatar_contradiction_clause,[],[f2963])).
% 2.81/0.75  fof(f2963,plain,(
% 2.81/0.75    $false | (~spl6_42 | spl6_43)),
% 2.81/0.75    inference(subsumption_resolution,[],[f2956,f816])).
% 2.81/0.75  fof(f816,plain,(
% 2.81/0.75    k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK1) | spl6_43),
% 2.81/0.75    inference(avatar_component_clause,[],[f814])).
% 2.81/0.75  fof(f2956,plain,(
% 2.81/0.75    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) | ~spl6_42),
% 2.81/0.75    inference(resolution,[],[f2947,f53])).
% 2.81/0.75  fof(f53,plain,(
% 2.81/0.75    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.81/0.75    inference(cnf_transformation,[],[f34])).
% 2.81/0.75  fof(f34,plain,(
% 2.81/0.75    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 2.81/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f33])).
% 2.81/0.75  fof(f33,plain,(
% 2.81/0.75    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.81/0.75    introduced(choice_axiom,[])).
% 2.81/0.75  fof(f22,plain,(
% 2.81/0.75    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.81/0.75    inference(ennf_transformation,[],[f6])).
% 2.81/0.75  fof(f6,axiom,(
% 2.81/0.75    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.81/0.75  fof(f2840,plain,(
% 2.81/0.75    spl6_42),
% 2.81/0.75    inference(avatar_contradiction_clause,[],[f2839])).
% 2.81/0.75  fof(f2839,plain,(
% 2.81/0.75    $false | spl6_42),
% 2.81/0.75    inference(subsumption_resolution,[],[f2828,f2766])).
% 2.81/0.75  fof(f2766,plain,(
% 2.81/0.75    ( ! [X0] : (~r1_xboole_0(sK1,X0)) ) | spl6_42),
% 2.81/0.75    inference(resolution,[],[f2494,f58])).
% 2.81/0.75  fof(f2494,plain,(
% 2.81/0.75    ( ! [X0] : (r2_hidden(sK3(k3_xboole_0(sK1,X0)),k3_xboole_0(sK1,X0))) ) | spl6_42),
% 2.81/0.75    inference(resolution,[],[f2152,f59])).
% 2.81/0.75  fof(f59,plain,(
% 2.81/0.75    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f8])).
% 2.81/0.75  fof(f8,axiom,(
% 2.81/0.75    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.81/0.75  fof(f2152,plain,(
% 2.81/0.75    ( ! [X0] : (~r1_tarski(X0,sK1) | r2_hidden(sK3(X0),X0)) ) | spl6_42),
% 2.81/0.75    inference(superposition,[],[f812,f53])).
% 2.81/0.75  fof(f812,plain,(
% 2.81/0.75    ~r1_tarski(k1_xboole_0,sK1) | spl6_42),
% 2.81/0.75    inference(avatar_component_clause,[],[f810])).
% 2.81/0.75  fof(f2828,plain,(
% 2.81/0.75    ( ! [X1] : (r1_xboole_0(sK1,k4_xboole_0(X1,sK1))) ) | spl6_42),
% 2.81/0.75    inference(resolution,[],[f2785,f61])).
% 2.81/0.75  fof(f2785,plain,(
% 2.81/0.75    ( ! [X4,X5] : (~r2_hidden(sK5(sK1,X4),k4_xboole_0(X5,sK1))) ) | spl6_42),
% 2.81/0.75    inference(resolution,[],[f2773,f64])).
% 2.81/0.75  fof(f2773,plain,(
% 2.81/0.75    ( ! [X0] : (r2_hidden(sK5(sK1,X0),sK1)) ) | spl6_42),
% 2.81/0.75    inference(resolution,[],[f2766,f60])).
% 2.81/0.75  % SZS output end Proof for theBenchmark
% 2.81/0.75  % (19327)------------------------------
% 2.81/0.75  % (19327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.75  % (19327)Termination reason: Refutation
% 2.81/0.75  
% 2.81/0.75  % (19327)Memory used [KB]: 10234
% 2.81/0.75  % (19327)Time elapsed: 0.334 s
% 2.81/0.75  % (19327)------------------------------
% 2.81/0.75  % (19327)------------------------------
% 2.81/0.76  % (19307)Success in time 0.396 s
%------------------------------------------------------------------------------
