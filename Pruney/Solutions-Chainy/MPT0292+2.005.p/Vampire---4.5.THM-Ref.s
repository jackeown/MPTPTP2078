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
% DateTime   : Thu Dec  3 12:41:47 EST 2020

% Result     : Theorem 2.09s
% Output     : Refutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 108 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  292 ( 497 expanded)
%              Number of equality atoms :   54 (  89 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f170,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f97,f110,f169])).

fof(f169,plain,
    ( ~ spl6_3
    | spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f162,f88,f84,f94])).

fof(f94,plain,
    ( spl6_3
  <=> r2_hidden(sK2(k1_zfmisc_1(sK0),sK0),sK3(k1_zfmisc_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f84,plain,
    ( spl6_1
  <=> r2_hidden(sK2(k1_zfmisc_1(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f88,plain,
    ( spl6_2
  <=> r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f162,plain,
    ( ~ r2_hidden(sK2(k1_zfmisc_1(sK0),sK0),sK3(k1_zfmisc_1(sK0),sK0))
    | spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f85,f160])).

fof(f160,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK3(k1_zfmisc_1(sK0),sK0))
        | r2_hidden(X4,sK0) )
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f153,f32])).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f153,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k4_xboole_0(sK3(k1_zfmisc_1(sK0),sK0),k1_xboole_0))
        | r2_hidden(X4,sK0) )
    | ~ spl6_2 ),
    inference(superposition,[],[f69,f129])).

fof(f129,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3(k1_zfmisc_1(sK0),sK0),sK0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f118,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f118,plain,
    ( r1_tarski(sK3(k1_zfmisc_1(sK0),sK0),sK0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f90,f64])).

fof(f64,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f90,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),k1_zfmisc_1(sK0))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f50,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f85,plain,
    ( ~ r2_hidden(sK2(k1_zfmisc_1(sK0),sK0),sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f110,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f62,f99,f63])).

fof(f63,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f99,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK0))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f31,f86,f86,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( k3_tarski(X0) = X1
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK2(X0,X1),X3)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK2(X0,X1),X3) )
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( ( r2_hidden(sK3(X0,X1),X0)
              & r2_hidden(sK2(X0,X1),sK3(X0,X1)) )
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK4(X0,X5),X0)
                & r2_hidden(X5,sK4(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f23,f22,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK2(X0,X1),X3) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK2(X0,X1),X4) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK2(X0,X1),X4) )
     => ( r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK4(X0,X5),X0)
        & r2_hidden(X5,sK4(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f86,plain,
    ( r2_hidden(sK2(k1_zfmisc_1(sK0),sK0),sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f31,plain,(
    sK0 != k3_tarski(k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    sK0 != k3_tarski(k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f11])).

fof(f11,plain,
    ( ? [X0] : k3_tarski(k1_zfmisc_1(X0)) != X0
   => sK0 != k3_tarski(k1_zfmisc_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] : k3_tarski(k1_zfmisc_1(X0)) != X0 ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f62,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f97,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f92,f94,f84])).

fof(f92,plain,
    ( r2_hidden(sK2(k1_zfmisc_1(sK0),sK0),sK3(k1_zfmisc_1(sK0),sK0))
    | r2_hidden(sK2(k1_zfmisc_1(sK0),sK0),sK0) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( sK0 != X0
      | r2_hidden(sK2(k1_zfmisc_1(sK0),X0),sK3(k1_zfmisc_1(sK0),X0))
      | r2_hidden(sK2(k1_zfmisc_1(sK0),X0),X0) ) ),
    inference(superposition,[],[f31,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK2(X0,X1),sK3(X0,X1))
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f91,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f82,f88,f84])).

fof(f82,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),k1_zfmisc_1(sK0))
    | r2_hidden(sK2(k1_zfmisc_1(sK0),sK0),sK0) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X1] :
      ( sK0 != X1
      | r2_hidden(sK3(k1_zfmisc_1(sK0),X1),k1_zfmisc_1(sK0))
      | r2_hidden(sK2(k1_zfmisc_1(sK0),X1),X1) ) ),
    inference(superposition,[],[f31,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK3(X0,X1),X0)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:46:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (952)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.51  % (954)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.51  % (969)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.51  % (950)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (977)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (953)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (948)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (949)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (976)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (946)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (944)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (946)Refutation not found, incomplete strategy% (946)------------------------------
% 0.22/0.53  % (946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (946)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (946)Memory used [KB]: 1663
% 0.22/0.53  % (946)Time elapsed: 0.113 s
% 0.22/0.53  % (946)------------------------------
% 0.22/0.53  % (946)------------------------------
% 0.22/0.53  % (967)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (967)Refutation not found, incomplete strategy% (967)------------------------------
% 0.22/0.53  % (967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (967)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (967)Memory used [KB]: 1663
% 0.22/0.53  % (967)Time elapsed: 0.081 s
% 0.22/0.53  % (967)------------------------------
% 0.22/0.53  % (967)------------------------------
% 0.22/0.53  % (980)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (980)Refutation not found, incomplete strategy% (980)------------------------------
% 0.22/0.53  % (980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (980)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (980)Memory used [KB]: 6140
% 0.22/0.53  % (947)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (980)Time elapsed: 0.118 s
% 0.22/0.53  % (980)------------------------------
% 0.22/0.53  % (980)------------------------------
% 0.22/0.53  % (972)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (972)Refutation not found, incomplete strategy% (972)------------------------------
% 0.22/0.53  % (972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (972)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (972)Memory used [KB]: 1663
% 0.22/0.53  % (972)Time elapsed: 0.120 s
% 0.22/0.53  % (972)------------------------------
% 0.22/0.53  % (972)------------------------------
% 0.22/0.53  % (974)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (982)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (966)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (965)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (978)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (978)Refutation not found, incomplete strategy% (978)------------------------------
% 0.22/0.54  % (978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (978)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (978)Memory used [KB]: 10618
% 0.22/0.54  % (978)Time elapsed: 0.128 s
% 0.22/0.54  % (978)------------------------------
% 0.22/0.54  % (978)------------------------------
% 0.22/0.54  % (979)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (971)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (979)Refutation not found, incomplete strategy% (979)------------------------------
% 0.22/0.54  % (979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (979)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (979)Memory used [KB]: 6140
% 0.22/0.54  % (979)Time elapsed: 0.127 s
% 0.22/0.54  % (979)------------------------------
% 0.22/0.54  % (979)------------------------------
% 0.22/0.55  % (951)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (973)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (981)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (964)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (983)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (981)Refutation not found, incomplete strategy% (981)------------------------------
% 0.22/0.55  % (981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (975)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (955)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (981)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (981)Memory used [KB]: 6140
% 0.22/0.55  % (981)Time elapsed: 0.141 s
% 0.22/0.55  % (981)------------------------------
% 0.22/0.55  % (981)------------------------------
% 0.22/0.55  % (982)Refutation not found, incomplete strategy% (982)------------------------------
% 0.22/0.55  % (982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (955)Refutation not found, incomplete strategy% (955)------------------------------
% 0.22/0.56  % (955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (982)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (982)Memory used [KB]: 10618
% 0.22/0.56  % (982)Time elapsed: 0.141 s
% 0.22/0.56  % (982)------------------------------
% 0.22/0.56  % (982)------------------------------
% 0.22/0.56  % (970)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (964)Refutation not found, incomplete strategy% (964)------------------------------
% 0.22/0.56  % (964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (964)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (964)Memory used [KB]: 6140
% 0.22/0.56  % (964)Time elapsed: 0.141 s
% 0.22/0.56  % (964)------------------------------
% 0.22/0.56  % (964)------------------------------
% 0.22/0.56  % (970)Refutation not found, incomplete strategy% (970)------------------------------
% 0.22/0.56  % (970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (955)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (955)Memory used [KB]: 10618
% 0.22/0.56  % (955)Time elapsed: 0.144 s
% 0.22/0.56  % (955)------------------------------
% 0.22/0.56  % (955)------------------------------
% 0.22/0.56  % (983)Refutation not found, incomplete strategy% (983)------------------------------
% 0.22/0.56  % (983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (983)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (983)Memory used [KB]: 1663
% 0.22/0.56  % (983)Time elapsed: 0.150 s
% 0.22/0.56  % (983)------------------------------
% 0.22/0.56  % (983)------------------------------
% 0.22/0.56  % (970)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (970)Memory used [KB]: 10618
% 0.22/0.56  % (970)Time elapsed: 0.143 s
% 0.22/0.56  % (970)------------------------------
% 0.22/0.56  % (970)------------------------------
% 0.22/0.57  % (971)Refutation not found, incomplete strategy% (971)------------------------------
% 0.22/0.57  % (971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (971)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (971)Memory used [KB]: 1663
% 0.22/0.57  % (971)Time elapsed: 0.138 s
% 0.22/0.57  % (971)------------------------------
% 0.22/0.57  % (971)------------------------------
% 2.04/0.64  % (984)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.09/0.66  % (947)Refutation not found, incomplete strategy% (947)------------------------------
% 2.09/0.66  % (947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.66  % (987)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.09/0.66  % (986)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.09/0.67  % (985)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.09/0.67  % (947)Termination reason: Refutation not found, incomplete strategy
% 2.09/0.67  
% 2.09/0.67  % (947)Memory used [KB]: 6140
% 2.09/0.67  % (947)Time elapsed: 0.249 s
% 2.09/0.67  % (947)------------------------------
% 2.09/0.67  % (947)------------------------------
% 2.09/0.67  % (988)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.09/0.67  % (988)Refutation not found, incomplete strategy% (988)------------------------------
% 2.09/0.67  % (988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.67  % (995)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.09/0.67  % (948)Refutation not found, incomplete strategy% (948)------------------------------
% 2.09/0.67  % (948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.67  % (948)Termination reason: Refutation not found, incomplete strategy
% 2.09/0.67  
% 2.09/0.67  % (948)Memory used [KB]: 6140
% 2.09/0.67  % (948)Time elapsed: 0.238 s
% 2.09/0.67  % (948)------------------------------
% 2.09/0.67  % (948)------------------------------
% 2.09/0.67  % (987)Refutation not found, incomplete strategy% (987)------------------------------
% 2.09/0.67  % (987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.67  % (987)Termination reason: Refutation not found, incomplete strategy
% 2.09/0.67  
% 2.09/0.67  % (987)Memory used [KB]: 10618
% 2.09/0.67  % (987)Time elapsed: 0.102 s
% 2.09/0.67  % (987)------------------------------
% 2.09/0.67  % (987)------------------------------
% 2.09/0.68  % (988)Termination reason: Refutation not found, incomplete strategy
% 2.09/0.68  
% 2.09/0.68  % (988)Memory used [KB]: 10618
% 2.09/0.68  % (988)Time elapsed: 0.099 s
% 2.09/0.68  % (988)------------------------------
% 2.09/0.68  % (988)------------------------------
% 2.09/0.68  % (991)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.09/0.68  % (990)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.09/0.68  % (998)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.09/0.69  % (990)Refutation not found, incomplete strategy% (990)------------------------------
% 2.09/0.69  % (990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.69  % (990)Termination reason: Refutation not found, incomplete strategy
% 2.09/0.69  
% 2.09/0.69  % (990)Memory used [KB]: 10746
% 2.09/0.69  % (990)Time elapsed: 0.097 s
% 2.09/0.69  % (990)------------------------------
% 2.09/0.69  % (990)------------------------------
% 2.09/0.69  % (996)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.09/0.69  % (989)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.09/0.69  % (996)Refutation not found, incomplete strategy% (996)------------------------------
% 2.09/0.69  % (996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.69  % (997)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.09/0.70  % (996)Termination reason: Refutation not found, incomplete strategy
% 2.09/0.70  
% 2.09/0.70  % (996)Memory used [KB]: 10746
% 2.09/0.70  % (996)Time elapsed: 0.105 s
% 2.09/0.70  % (996)------------------------------
% 2.09/0.70  % (996)------------------------------
% 2.09/0.70  % (998)Refutation found. Thanks to Tanya!
% 2.09/0.70  % SZS status Theorem for theBenchmark
% 2.09/0.70  % SZS output start Proof for theBenchmark
% 2.09/0.70  fof(f170,plain,(
% 2.09/0.70    $false),
% 2.09/0.70    inference(avatar_sat_refutation,[],[f91,f97,f110,f169])).
% 2.09/0.70  fof(f169,plain,(
% 2.09/0.70    ~spl6_3 | spl6_1 | ~spl6_2),
% 2.09/0.70    inference(avatar_split_clause,[],[f162,f88,f84,f94])).
% 2.09/0.70  fof(f94,plain,(
% 2.09/0.70    spl6_3 <=> r2_hidden(sK2(k1_zfmisc_1(sK0),sK0),sK3(k1_zfmisc_1(sK0),sK0))),
% 2.09/0.70    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.09/0.70  fof(f84,plain,(
% 2.09/0.70    spl6_1 <=> r2_hidden(sK2(k1_zfmisc_1(sK0),sK0),sK0)),
% 2.09/0.70    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.09/0.70  fof(f88,plain,(
% 2.09/0.70    spl6_2 <=> r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),k1_zfmisc_1(sK0))),
% 2.09/0.70    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.09/0.70  fof(f162,plain,(
% 2.09/0.70    ~r2_hidden(sK2(k1_zfmisc_1(sK0),sK0),sK3(k1_zfmisc_1(sK0),sK0)) | (spl6_1 | ~spl6_2)),
% 2.09/0.70    inference(unit_resulting_resolution,[],[f85,f160])).
% 2.09/0.70  fof(f160,plain,(
% 2.09/0.70    ( ! [X4] : (~r2_hidden(X4,sK3(k1_zfmisc_1(sK0),sK0)) | r2_hidden(X4,sK0)) ) | ~spl6_2),
% 2.09/0.70    inference(forward_demodulation,[],[f153,f32])).
% 2.09/0.70  fof(f32,plain,(
% 2.09/0.70    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.09/0.70    inference(cnf_transformation,[],[f4])).
% 2.09/0.70  fof(f4,axiom,(
% 2.09/0.70    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.09/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.09/0.70  fof(f153,plain,(
% 2.09/0.70    ( ! [X4] : (~r2_hidden(X4,k4_xboole_0(sK3(k1_zfmisc_1(sK0),sK0),k1_xboole_0)) | r2_hidden(X4,sK0)) ) | ~spl6_2),
% 2.09/0.70    inference(superposition,[],[f69,f129])).
% 2.09/0.70  fof(f129,plain,(
% 2.09/0.70    k1_xboole_0 = k4_xboole_0(sK3(k1_zfmisc_1(sK0),sK0),sK0) | ~spl6_2),
% 2.09/0.70    inference(unit_resulting_resolution,[],[f118,f48])).
% 2.09/0.70  fof(f48,plain,(
% 2.09/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.09/0.70    inference(cnf_transformation,[],[f25])).
% 2.09/0.70  fof(f25,plain,(
% 2.09/0.70    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.09/0.70    inference(nnf_transformation,[],[f3])).
% 2.09/0.70  fof(f3,axiom,(
% 2.09/0.70    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.09/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.09/0.70  fof(f118,plain,(
% 2.09/0.70    r1_tarski(sK3(k1_zfmisc_1(sK0),sK0),sK0) | ~spl6_2),
% 2.09/0.70    inference(unit_resulting_resolution,[],[f90,f64])).
% 2.09/0.70  fof(f64,plain,(
% 2.09/0.70    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 2.09/0.70    inference(equality_resolution,[],[f37])).
% 2.09/0.70  fof(f37,plain,(
% 2.09/0.70    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.09/0.70    inference(cnf_transformation,[],[f18])).
% 2.09/0.70  fof(f18,plain,(
% 2.09/0.70    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.09/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).
% 2.09/0.70  fof(f17,plain,(
% 2.09/0.70    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 2.09/0.70    introduced(choice_axiom,[])).
% 2.09/0.70  fof(f16,plain,(
% 2.09/0.70    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.09/0.70    inference(rectify,[],[f15])).
% 2.09/0.70  fof(f15,plain,(
% 2.09/0.70    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.09/0.70    inference(nnf_transformation,[],[f6])).
% 2.09/0.70  fof(f6,axiom,(
% 2.09/0.70    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.09/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.09/0.70  fof(f90,plain,(
% 2.09/0.70    r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),k1_zfmisc_1(sK0)) | ~spl6_2),
% 2.09/0.70    inference(avatar_component_clause,[],[f88])).
% 2.09/0.70  fof(f69,plain,(
% 2.09/0.70    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.09/0.70    inference(equality_resolution,[],[f59])).
% 2.09/0.70  fof(f59,plain,(
% 2.09/0.70    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 2.09/0.70    inference(definition_unfolding,[],[f50,f33])).
% 2.09/0.70  fof(f33,plain,(
% 2.09/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.09/0.70    inference(cnf_transformation,[],[f5])).
% 2.09/0.70  fof(f5,axiom,(
% 2.09/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.09/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.09/0.70  fof(f50,plain,(
% 2.09/0.70    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.09/0.70    inference(cnf_transformation,[],[f30])).
% 2.09/0.70  fof(f30,plain,(
% 2.09/0.70    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.09/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).
% 2.09/0.70  fof(f29,plain,(
% 2.09/0.70    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 2.09/0.70    introduced(choice_axiom,[])).
% 2.09/0.70  fof(f28,plain,(
% 2.09/0.70    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.09/0.70    inference(rectify,[],[f27])).
% 2.09/0.70  fof(f27,plain,(
% 2.09/0.70    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.09/0.70    inference(flattening,[],[f26])).
% 2.09/0.70  fof(f26,plain,(
% 2.09/0.70    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.09/0.70    inference(nnf_transformation,[],[f1])).
% 2.09/0.70  fof(f1,axiom,(
% 2.09/0.70    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.09/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.09/0.70  fof(f85,plain,(
% 2.09/0.70    ~r2_hidden(sK2(k1_zfmisc_1(sK0),sK0),sK0) | spl6_1),
% 2.09/0.70    inference(avatar_component_clause,[],[f84])).
% 2.09/0.70  fof(f110,plain,(
% 2.09/0.70    ~spl6_1),
% 2.09/0.70    inference(avatar_contradiction_clause,[],[f105])).
% 2.09/0.70  fof(f105,plain,(
% 2.09/0.70    $false | ~spl6_1),
% 2.09/0.70    inference(unit_resulting_resolution,[],[f62,f99,f63])).
% 2.09/0.70  fof(f63,plain,(
% 2.09/0.70    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 2.09/0.70    inference(equality_resolution,[],[f38])).
% 2.09/0.70  fof(f38,plain,(
% 2.09/0.70    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 2.09/0.70    inference(cnf_transformation,[],[f18])).
% 2.09/0.70  fof(f99,plain,(
% 2.09/0.70    ~r2_hidden(sK0,k1_zfmisc_1(sK0)) | ~spl6_1),
% 2.09/0.70    inference(unit_resulting_resolution,[],[f31,f86,f86,f46])).
% 2.09/0.70  fof(f46,plain,(
% 2.09/0.70    ( ! [X0,X3,X1] : (k3_tarski(X0) = X1 | ~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 2.09/0.70    inference(cnf_transformation,[],[f24])).
% 2.09/0.70  fof(f24,plain,(
% 2.09/0.70    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & ((r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),sK3(X0,X1))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 2.09/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f23,f22,f21])).
% 2.09/0.70  fof(f21,plain,(
% 2.09/0.70    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK2(X0,X1),X4)) | r2_hidden(sK2(X0,X1),X1))))),
% 2.09/0.70    introduced(choice_axiom,[])).
% 2.09/0.70  fof(f22,plain,(
% 2.09/0.70    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK2(X0,X1),X4)) => (r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),sK3(X0,X1))))),
% 2.09/0.70    introduced(choice_axiom,[])).
% 2.09/0.70  fof(f23,plain,(
% 2.09/0.70    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))))),
% 2.09/0.70    introduced(choice_axiom,[])).
% 2.09/0.70  fof(f20,plain,(
% 2.09/0.70    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 2.09/0.70    inference(rectify,[],[f19])).
% 2.09/0.70  fof(f19,plain,(
% 2.09/0.70    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 2.09/0.70    inference(nnf_transformation,[],[f7])).
% 2.09/0.70  fof(f7,axiom,(
% 2.09/0.70    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 2.09/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 2.09/0.70  fof(f86,plain,(
% 2.09/0.70    r2_hidden(sK2(k1_zfmisc_1(sK0),sK0),sK0) | ~spl6_1),
% 2.09/0.70    inference(avatar_component_clause,[],[f84])).
% 2.09/0.70  fof(f31,plain,(
% 2.09/0.70    sK0 != k3_tarski(k1_zfmisc_1(sK0))),
% 2.09/0.70    inference(cnf_transformation,[],[f12])).
% 2.09/0.70  fof(f12,plain,(
% 2.09/0.70    sK0 != k3_tarski(k1_zfmisc_1(sK0))),
% 2.09/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f11])).
% 2.09/0.70  fof(f11,plain,(
% 2.09/0.70    ? [X0] : k3_tarski(k1_zfmisc_1(X0)) != X0 => sK0 != k3_tarski(k1_zfmisc_1(sK0))),
% 2.09/0.70    introduced(choice_axiom,[])).
% 2.09/0.70  fof(f10,plain,(
% 2.09/0.70    ? [X0] : k3_tarski(k1_zfmisc_1(X0)) != X0),
% 2.09/0.70    inference(ennf_transformation,[],[f9])).
% 2.09/0.70  fof(f9,negated_conjecture,(
% 2.09/0.70    ~! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 2.09/0.70    inference(negated_conjecture,[],[f8])).
% 2.09/0.70  fof(f8,conjecture,(
% 2.09/0.70    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 2.09/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 2.09/0.70  fof(f62,plain,(
% 2.09/0.70    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.09/0.70    inference(equality_resolution,[],[f34])).
% 2.09/0.70  fof(f34,plain,(
% 2.09/0.70    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.09/0.70    inference(cnf_transformation,[],[f14])).
% 2.09/0.70  fof(f14,plain,(
% 2.09/0.70    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.09/0.70    inference(flattening,[],[f13])).
% 2.09/0.70  fof(f13,plain,(
% 2.09/0.70    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.09/0.70    inference(nnf_transformation,[],[f2])).
% 2.09/0.70  fof(f2,axiom,(
% 2.09/0.70    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.09/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.09/0.70  fof(f97,plain,(
% 2.09/0.70    spl6_1 | spl6_3),
% 2.09/0.70    inference(avatar_split_clause,[],[f92,f94,f84])).
% 2.09/0.70  fof(f92,plain,(
% 2.09/0.70    r2_hidden(sK2(k1_zfmisc_1(sK0),sK0),sK3(k1_zfmisc_1(sK0),sK0)) | r2_hidden(sK2(k1_zfmisc_1(sK0),sK0),sK0)),
% 2.09/0.70    inference(equality_resolution,[],[f73])).
% 2.09/0.70  fof(f73,plain,(
% 2.09/0.70    ( ! [X0] : (sK0 != X0 | r2_hidden(sK2(k1_zfmisc_1(sK0),X0),sK3(k1_zfmisc_1(sK0),X0)) | r2_hidden(sK2(k1_zfmisc_1(sK0),X0),X0)) )),
% 2.09/0.70    inference(superposition,[],[f31,f44])).
% 2.09/0.70  fof(f44,plain,(
% 2.09/0.70    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(sK2(X0,X1),X1)) )),
% 2.09/0.70    inference(cnf_transformation,[],[f24])).
% 2.09/0.70  fof(f91,plain,(
% 2.09/0.70    spl6_1 | spl6_2),
% 2.09/0.70    inference(avatar_split_clause,[],[f82,f88,f84])).
% 2.09/0.70  fof(f82,plain,(
% 2.09/0.70    r2_hidden(sK3(k1_zfmisc_1(sK0),sK0),k1_zfmisc_1(sK0)) | r2_hidden(sK2(k1_zfmisc_1(sK0),sK0),sK0)),
% 2.09/0.70    inference(equality_resolution,[],[f74])).
% 2.09/0.70  fof(f74,plain,(
% 2.09/0.70    ( ! [X1] : (sK0 != X1 | r2_hidden(sK3(k1_zfmisc_1(sK0),X1),k1_zfmisc_1(sK0)) | r2_hidden(sK2(k1_zfmisc_1(sK0),X1),X1)) )),
% 2.09/0.70    inference(superposition,[],[f31,f45])).
% 2.09/0.70  fof(f45,plain,(
% 2.09/0.70    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK3(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)) )),
% 2.09/0.70    inference(cnf_transformation,[],[f24])).
% 2.09/0.70  % SZS output end Proof for theBenchmark
% 2.09/0.70  % (998)------------------------------
% 2.09/0.70  % (998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.70  % (998)Termination reason: Refutation
% 2.09/0.70  
% 2.09/0.70  % (998)Memory used [KB]: 10746
% 2.09/0.70  % (998)Time elapsed: 0.096 s
% 2.09/0.70  % (998)------------------------------
% 2.09/0.70  % (998)------------------------------
% 2.61/0.71  % (943)Success in time 0.328 s
%------------------------------------------------------------------------------
