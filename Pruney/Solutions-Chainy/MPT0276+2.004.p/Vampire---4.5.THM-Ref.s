%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:28 EST 2020

% Result     : Theorem 3.18s
% Output     : Refutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 522 expanded)
%              Number of leaves         :   43 ( 197 expanded)
%              Depth                    :   14
%              Number of atoms          :  583 (2275 expanded)
%              Number of equality atoms :  187 ( 926 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f778,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f103,f108,f113,f155,f193,f332,f373,f374,f392,f410,f425,f429,f529,f538,f540,f541,f569,f677,f685,f686,f687,f688,f689,f735,f761,f762,f763,f764,f769,f771,f772])).

fof(f772,plain,
    ( ~ spl5_8
    | spl5_6
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f402,f385,f152,f175])).

fof(f175,plain,
    ( spl5_8
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f152,plain,
    ( spl5_6
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f385,plain,
    ( spl5_23
  <=> sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f402,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_6
    | ~ spl5_23 ),
    inference(superposition,[],[f154,f387])).

fof(f387,plain,
    ( sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f385])).

fof(f154,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f152])).

fof(f771,plain,
    ( spl5_7
    | ~ spl5_21
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f553,f535,f358,f171])).

fof(f171,plain,
    ( spl5_7
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f358,plain,
    ( spl5_21
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f535,plain,
    ( spl5_32
  <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f553,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_21
    | ~ spl5_32 ),
    inference(superposition,[],[f359,f537])).

fof(f537,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f535])).

fof(f359,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f358])).

fof(f769,plain,
    ( spl5_8
    | spl5_2
    | ~ spl5_27
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f768,f493,f422,f100,f175])).

fof(f100,plain,
    ( spl5_2
  <=> k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f422,plain,
    ( spl5_27
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f493,plain,
    ( spl5_30
  <=> sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f768,plain,
    ( r2_hidden(sK1,sK2)
    | spl5_2
    | ~ spl5_27
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f767,f90])).

fof(f90,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f50,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f767,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(sK1,sK2)
    | spl5_2
    | ~ spl5_27
    | ~ spl5_30 ),
    inference(forward_demodulation,[],[f766,f495])).

fof(f495,plain,
    ( sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f493])).

fof(f766,plain,
    ( r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_2
    | ~ spl5_27
    | ~ spl5_30 ),
    inference(forward_demodulation,[],[f765,f495])).

fof(f765,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_2
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f740,f424])).

fof(f424,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f422])).

fof(f740,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_2 ),
    inference(equality_resolution,[],[f199])).

fof(f199,plain,
    ( ! [X1] :
        ( k2_enumset1(sK1,sK1,sK1,sK1) != X1
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),sK2)
        | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),k2_enumset1(sK0,sK0,sK0,sK1))
        | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),X1) )
    | spl5_2 ),
    inference(superposition,[],[f102,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f47,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).

fof(f20,plain,(
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

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f102,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK1,sK1,sK1,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f764,plain,
    ( sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f763,plain,
    ( sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f762,plain,
    ( sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f761,plain,
    ( spl5_16
    | ~ spl5_34 ),
    inference(avatar_contradiction_clause,[],[f760])).

fof(f760,plain,
    ( $false
    | spl5_16
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f759,f90])).

fof(f759,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_16
    | ~ spl5_34 ),
    inference(forward_demodulation,[],[f326,f568])).

fof(f568,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f566])).

fof(f566,plain,
    ( spl5_34
  <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f326,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f325])).

fof(f325,plain,
    ( spl5_16
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f735,plain,
    ( ~ spl5_16
    | ~ spl5_25
    | spl5_3
    | spl5_17 ),
    inference(avatar_split_clause,[],[f734,f329,f105,f407,f325])).

fof(f407,plain,
    ( spl5_25
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f105,plain,
    ( spl5_3
  <=> k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f329,plain,
    ( spl5_17
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f734,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_3
    | spl5_17 ),
    inference(subsumption_resolution,[],[f732,f331])).

fof(f331,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f329])).

fof(f732,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2)
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_3 ),
    inference(equality_resolution,[],[f198])).

fof(f198,plain,
    ( ! [X0] :
        ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),sK2)
        | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),k2_enumset1(sK0,sK0,sK0,sK1))
        | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X0) )
    | spl5_3 ),
    inference(superposition,[],[f107,f66])).

fof(f107,plain,
    ( k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f689,plain,
    ( spl5_34
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f581,f325,f566])).

fof(f581,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_16 ),
    inference(duplicate_literal_removal,[],[f577])).

fof(f577,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_16 ),
    inference(resolution,[],[f327,f93])).

fof(f93,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f48,f60])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f327,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f325])).

fof(f688,plain,
    ( spl5_30
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f491,f340,f493])).

fof(f340,plain,
    ( spl5_18
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f491,plain,
    ( sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_18 ),
    inference(duplicate_literal_removal,[],[f487])).

fof(f487,plain,
    ( sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_18 ),
    inference(resolution,[],[f342,f93])).

fof(f342,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f340])).

fof(f687,plain,
    ( spl5_30
    | spl5_38
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f667,f422,f673,f493])).

fof(f673,plain,
    ( spl5_38
  <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f667,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_27 ),
    inference(resolution,[],[f424,f93])).

fof(f686,plain,
    ( spl5_18
    | ~ spl5_19
    | spl5_2 ),
    inference(avatar_split_clause,[],[f549,f100,f344,f340])).

fof(f344,plain,
    ( spl5_19
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f549,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_2 ),
    inference(equality_resolution,[],[f126])).

fof(f126,plain,
    ( ! [X1] :
        ( k2_enumset1(sK1,sK1,sK1,sK1) != X1
        | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),sK2)
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),X1) )
    | spl5_2 ),
    inference(superposition,[],[f102,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f46,f37])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f685,plain,
    ( sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2)
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f677,plain,
    ( sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f569,plain,
    ( spl5_33
    | spl5_34
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f557,f407,f566,f562])).

fof(f562,plain,
    ( spl5_33
  <=> sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f557,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_25 ),
    inference(resolution,[],[f409,f93])).

fof(f409,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f407])).

fof(f541,plain,
    ( sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f540,plain,
    ( sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)
    | r2_hidden(sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f538,plain,
    ( spl5_31
    | spl5_32
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f526,f354,f535,f531])).

fof(f531,plain,
    ( spl5_31
  <=> sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f354,plain,
    ( spl5_20
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f526,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl5_20 ),
    inference(resolution,[],[f356,f93])).

fof(f356,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f354])).

fof(f529,plain,
    ( spl5_1
    | ~ spl5_20
    | spl5_21 ),
    inference(avatar_contradiction_clause,[],[f525])).

fof(f525,plain,
    ( $false
    | spl5_1
    | ~ spl5_20
    | spl5_21 ),
    inference(unit_resulting_resolution,[],[f360,f356,f97,f356,f66])).

fof(f97,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl5_1
  <=> k2_enumset1(sK0,sK0,sK0,sK1) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f360,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)
    | spl5_21 ),
    inference(avatar_component_clause,[],[f358])).

fof(f429,plain,
    ( spl5_20
    | spl5_1 ),
    inference(avatar_split_clause,[],[f428,f95,f354])).

fof(f428,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | spl5_1 ),
    inference(duplicate_literal_removal,[],[f427])).

fof(f427,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | spl5_1 ),
    inference(equality_resolution,[],[f138])).

fof(f138,plain,
    ( ! [X2] :
        ( k2_enumset1(sK0,sK0,sK0,sK1) != X2
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X2),k2_enumset1(sK0,sK0,sK0,sK1))
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X2),X2) )
    | spl5_1 ),
    inference(superposition,[],[f97,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f45,f37])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f425,plain,
    ( spl5_18
    | spl5_27
    | spl5_2 ),
    inference(avatar_split_clause,[],[f419,f100,f422,f340])).

fof(f419,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_2 ),
    inference(equality_resolution,[],[f137])).

fof(f137,plain,
    ( ! [X1] :
        ( k2_enumset1(sK1,sK1,sK1,sK1) != X1
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),k2_enumset1(sK0,sK0,sK0,sK1))
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),X1) )
    | spl5_2 ),
    inference(superposition,[],[f102,f68])).

fof(f410,plain,
    ( spl5_16
    | spl5_25
    | spl5_3 ),
    inference(avatar_split_clause,[],[f404,f105,f407,f325])).

fof(f404,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_3 ),
    inference(equality_resolution,[],[f136])).

fof(f136,plain,
    ( ! [X0] :
        ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),k2_enumset1(sK0,sK0,sK0,sK1))
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X0) )
    | spl5_3 ),
    inference(superposition,[],[f107,f68])).

fof(f392,plain,
    ( spl5_23
    | spl5_24
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f382,f366,f389,f385])).

fof(f389,plain,
    ( spl5_24
  <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f366,plain,
    ( spl5_22
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f382,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ spl5_22 ),
    inference(resolution,[],[f368,f93])).

fof(f368,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f366])).

fof(f374,plain,
    ( spl5_22
    | spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f364,f148,f110,f366])).

fof(f110,plain,
    ( spl5_4
  <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f148,plain,
    ( spl5_5
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f364,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))
    | spl5_4
    | spl5_5 ),
    inference(subsumption_resolution,[],[f363,f149])).

fof(f149,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f148])).

fof(f363,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | spl5_4 ),
    inference(equality_resolution,[],[f139])).

fof(f139,plain,
    ( ! [X3] :
        ( k1_xboole_0 != X3
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X3),k2_enumset1(sK0,sK0,sK0,sK1))
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X3),X3) )
    | spl5_4 ),
    inference(superposition,[],[f112,f68])).

fof(f112,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f373,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f372])).

fof(f372,plain,
    ( $false
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f150,f168])).

fof(f168,plain,(
    ! [X24,X23,X25,X22] :
      ( ~ r2_hidden(X25,k1_xboole_0)
      | ~ r2_hidden(X25,X24)
      | ~ r2_hidden(X23,X24)
      | ~ r2_hidden(X22,X24) ) ),
    inference(superposition,[],[f87,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k3_xboole_0(k2_enumset1(X0,X0,X0,X1),X2))
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f59,f37,f60])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f43,f37])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f150,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f148])).

fof(f332,plain,
    ( spl5_16
    | ~ spl5_17
    | spl5_3 ),
    inference(avatar_split_clause,[],[f322,f105,f329,f325])).

fof(f322,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_3 ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,
    ( ! [X0] :
        ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
        | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),sK2)
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X0) )
    | spl5_3 ),
    inference(superposition,[],[f107,f67])).

fof(f193,plain,
    ( ~ spl5_7
    | ~ spl5_8
    | spl5_4 ),
    inference(avatar_split_clause,[],[f169,f110,f175,f171])).

fof(f169,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | spl5_4 ),
    inference(trivial_inequality_removal,[],[f161])).

fof(f161,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | spl5_4 ),
    inference(superposition,[],[f112,f81])).

fof(f155,plain,
    ( spl5_5
    | ~ spl5_6
    | spl5_4 ),
    inference(avatar_split_clause,[],[f146,f110,f152,f148])).

fof(f146,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | spl5_4 ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,
    ( ! [X3] :
        ( k1_xboole_0 != X3
        | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X3),sK2)
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X3),X3) )
    | spl5_4 ),
    inference(superposition,[],[f112,f67])).

fof(f113,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f65,f110])).

fof(f65,plain,(
    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f31,f37,f60])).

fof(f31,plain,(
    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)
    & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
    & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
   => ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
      & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)
      & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
      & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
      & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
          & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_zfmisc_1)).

fof(f108,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f64,f105])).

fof(f64,plain,(
    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f32,f37,f60,f61])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f60])).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f103,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f63,f100])).

fof(f63,plain,(
    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f33,f37,f60,f61])).

fof(f33,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f98,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f62,f95])).

fof(f62,plain,(
    k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f34,f60,f37,f60])).

fof(f34,plain,(
    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:46:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (21220)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  % (21212)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (21235)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.51  % (21217)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (21221)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (21229)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (21218)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (21228)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (21215)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (21213)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (21219)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (21227)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (21231)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (21235)Refutation not found, incomplete strategy% (21235)------------------------------
% 0.21/0.53  % (21235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21208)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (21235)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21235)Memory used [KB]: 6140
% 0.21/0.53  % (21235)Time elapsed: 0.113 s
% 0.21/0.53  % (21235)------------------------------
% 0.21/0.53  % (21235)------------------------------
% 0.21/0.53  % (21211)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (21224)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (21210)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (21232)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (21236)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (21222)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (21222)Refutation not found, incomplete strategy% (21222)------------------------------
% 0.21/0.54  % (21222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21222)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21222)Memory used [KB]: 1663
% 0.21/0.54  % (21222)Time elapsed: 0.132 s
% 0.21/0.54  % (21222)------------------------------
% 0.21/0.54  % (21222)------------------------------
% 0.21/0.54  % (21232)Refutation not found, incomplete strategy% (21232)------------------------------
% 0.21/0.54  % (21232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21224)Refutation not found, incomplete strategy% (21224)------------------------------
% 0.21/0.54  % (21224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21224)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21224)Memory used [KB]: 10618
% 0.21/0.54  % (21224)Time elapsed: 0.118 s
% 0.21/0.54  % (21224)------------------------------
% 0.21/0.54  % (21224)------------------------------
% 0.21/0.54  % (21209)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (21234)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (21232)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21232)Memory used [KB]: 10618
% 0.21/0.55  % (21232)Time elapsed: 0.119 s
% 0.21/0.55  % (21232)------------------------------
% 0.21/0.55  % (21232)------------------------------
% 0.21/0.55  % (21214)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (21234)Refutation not found, incomplete strategy% (21234)------------------------------
% 0.21/0.55  % (21234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21234)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21234)Memory used [KB]: 6140
% 0.21/0.55  % (21234)Time elapsed: 0.140 s
% 0.21/0.55  % (21234)------------------------------
% 0.21/0.55  % (21234)------------------------------
% 0.21/0.55  % (21233)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (21226)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (21226)Refutation not found, incomplete strategy% (21226)------------------------------
% 0.21/0.55  % (21226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21226)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21226)Memory used [KB]: 1663
% 0.21/0.55  % (21226)Time elapsed: 0.142 s
% 0.21/0.55  % (21226)------------------------------
% 0.21/0.55  % (21226)------------------------------
% 0.21/0.55  % (21237)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (21237)Refutation not found, incomplete strategy% (21237)------------------------------
% 0.21/0.55  % (21237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21237)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21237)Memory used [KB]: 1663
% 0.21/0.55  % (21237)Time elapsed: 0.147 s
% 0.21/0.55  % (21237)------------------------------
% 0.21/0.55  % (21237)------------------------------
% 0.21/0.56  % (21225)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (21223)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (21209)Refutation not found, incomplete strategy% (21209)------------------------------
% 0.21/0.56  % (21209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (21209)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (21209)Memory used [KB]: 1663
% 0.21/0.56  % (21209)Time elapsed: 0.151 s
% 0.21/0.56  % (21209)------------------------------
% 0.21/0.56  % (21209)------------------------------
% 0.21/0.56  % (21230)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (21216)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.57  % (21225)Refutation not found, incomplete strategy% (21225)------------------------------
% 0.21/0.57  % (21225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (21225)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (21225)Memory used [KB]: 1663
% 0.21/0.57  % (21225)Time elapsed: 0.169 s
% 0.21/0.57  % (21225)------------------------------
% 0.21/0.57  % (21225)------------------------------
% 2.26/0.65  % (21238)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.26/0.67  % (21211)Refutation not found, incomplete strategy% (21211)------------------------------
% 2.26/0.67  % (21211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.67  % (21211)Termination reason: Refutation not found, incomplete strategy
% 2.26/0.67  
% 2.26/0.67  % (21211)Memory used [KB]: 6140
% 2.26/0.67  % (21211)Time elapsed: 0.259 s
% 2.26/0.67  % (21211)------------------------------
% 2.26/0.67  % (21211)------------------------------
% 2.26/0.69  % (21240)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.26/0.70  % (21241)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.26/0.70  % (21242)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.26/0.70  % (21245)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.26/0.70  % (21242)Refutation not found, incomplete strategy% (21242)------------------------------
% 2.26/0.70  % (21242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.70  % (21242)Termination reason: Refutation not found, incomplete strategy
% 2.26/0.70  
% 2.26/0.70  % (21242)Memory used [KB]: 10618
% 2.26/0.70  % (21242)Time elapsed: 0.051 s
% 2.26/0.70  % (21242)------------------------------
% 2.26/0.70  % (21242)------------------------------
% 2.26/0.70  % (21246)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.26/0.72  % (21244)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.26/0.72  % (21243)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.26/0.73  % (21239)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.18/0.81  % (21210)Time limit reached!
% 3.18/0.81  % (21210)------------------------------
% 3.18/0.81  % (21210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.18/0.81  % (21210)Termination reason: Time limit
% 3.18/0.81  % (21210)Termination phase: Saturation
% 3.18/0.81  
% 3.18/0.81  % (21210)Memory used [KB]: 7675
% 3.18/0.81  % (21210)Time elapsed: 0.408 s
% 3.18/0.81  % (21210)------------------------------
% 3.18/0.81  % (21210)------------------------------
% 3.18/0.82  % (21248)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 3.18/0.83  % (21247)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 3.18/0.83  % (21239)Refutation found. Thanks to Tanya!
% 3.18/0.83  % SZS status Theorem for theBenchmark
% 3.18/0.83  % SZS output start Proof for theBenchmark
% 3.18/0.83  fof(f778,plain,(
% 3.18/0.83    $false),
% 3.18/0.83    inference(avatar_sat_refutation,[],[f98,f103,f108,f113,f155,f193,f332,f373,f374,f392,f410,f425,f429,f529,f538,f540,f541,f569,f677,f685,f686,f687,f688,f689,f735,f761,f762,f763,f764,f769,f771,f772])).
% 3.18/0.83  fof(f772,plain,(
% 3.18/0.83    ~spl5_8 | spl5_6 | ~spl5_23),
% 3.18/0.83    inference(avatar_split_clause,[],[f402,f385,f152,f175])).
% 3.18/0.83  fof(f175,plain,(
% 3.18/0.83    spl5_8 <=> r2_hidden(sK1,sK2)),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 3.18/0.83  fof(f152,plain,(
% 3.18/0.83    spl5_6 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2)),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 3.18/0.83  fof(f385,plain,(
% 3.18/0.83    spl5_23 <=> sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 3.18/0.83  fof(f402,plain,(
% 3.18/0.83    ~r2_hidden(sK1,sK2) | (spl5_6 | ~spl5_23)),
% 3.18/0.83    inference(superposition,[],[f154,f387])).
% 3.18/0.83  fof(f387,plain,(
% 3.18/0.83    sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | ~spl5_23),
% 3.18/0.83    inference(avatar_component_clause,[],[f385])).
% 3.18/0.83  fof(f154,plain,(
% 3.18/0.83    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2) | spl5_6),
% 3.18/0.83    inference(avatar_component_clause,[],[f152])).
% 3.18/0.83  fof(f771,plain,(
% 3.18/0.83    spl5_7 | ~spl5_21 | ~spl5_32),
% 3.18/0.83    inference(avatar_split_clause,[],[f553,f535,f358,f171])).
% 3.18/0.83  fof(f171,plain,(
% 3.18/0.83    spl5_7 <=> r2_hidden(sK0,sK2)),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 3.18/0.83  fof(f358,plain,(
% 3.18/0.83    spl5_21 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 3.18/0.83  fof(f535,plain,(
% 3.18/0.83    spl5_32 <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 3.18/0.83  fof(f553,plain,(
% 3.18/0.83    r2_hidden(sK0,sK2) | (~spl5_21 | ~spl5_32)),
% 3.18/0.83    inference(superposition,[],[f359,f537])).
% 3.18/0.83  fof(f537,plain,(
% 3.18/0.83    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl5_32),
% 3.18/0.83    inference(avatar_component_clause,[],[f535])).
% 3.18/0.83  fof(f359,plain,(
% 3.18/0.83    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) | ~spl5_21),
% 3.18/0.83    inference(avatar_component_clause,[],[f358])).
% 3.18/0.83  fof(f769,plain,(
% 3.18/0.83    spl5_8 | spl5_2 | ~spl5_27 | ~spl5_30),
% 3.18/0.83    inference(avatar_split_clause,[],[f768,f493,f422,f100,f175])).
% 3.18/0.83  fof(f100,plain,(
% 3.18/0.83    spl5_2 <=> k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 3.18/0.83  fof(f422,plain,(
% 3.18/0.83    spl5_27 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 3.18/0.83  fof(f493,plain,(
% 3.18/0.83    spl5_30 <=> sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 3.18/0.83  fof(f768,plain,(
% 3.18/0.83    r2_hidden(sK1,sK2) | (spl5_2 | ~spl5_27 | ~spl5_30)),
% 3.18/0.83    inference(subsumption_resolution,[],[f767,f90])).
% 3.18/0.83  fof(f90,plain,(
% 3.18/0.83    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 3.18/0.83    inference(equality_resolution,[],[f89])).
% 3.18/0.83  fof(f89,plain,(
% 3.18/0.83    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 3.18/0.83    inference(equality_resolution,[],[f75])).
% 3.18/0.83  fof(f75,plain,(
% 3.18/0.83    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.18/0.83    inference(definition_unfolding,[],[f50,f60])).
% 3.18/0.83  fof(f60,plain,(
% 3.18/0.83    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.18/0.83    inference(definition_unfolding,[],[f36,f41])).
% 3.18/0.83  fof(f41,plain,(
% 3.18/0.83    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.18/0.83    inference(cnf_transformation,[],[f7])).
% 3.18/0.83  fof(f7,axiom,(
% 3.18/0.83    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.18/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 3.18/0.83  fof(f36,plain,(
% 3.18/0.83    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.18/0.83    inference(cnf_transformation,[],[f6])).
% 3.18/0.83  fof(f6,axiom,(
% 3.18/0.83    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.18/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.18/0.83  fof(f50,plain,(
% 3.18/0.83    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.18/0.83    inference(cnf_transformation,[],[f26])).
% 3.18/0.83  fof(f26,plain,(
% 3.18/0.83    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.18/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 3.18/0.83  fof(f25,plain,(
% 3.18/0.83    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 3.18/0.83    introduced(choice_axiom,[])).
% 3.18/0.83  fof(f24,plain,(
% 3.18/0.83    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.18/0.83    inference(rectify,[],[f23])).
% 3.18/0.83  fof(f23,plain,(
% 3.18/0.83    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.18/0.83    inference(flattening,[],[f22])).
% 3.18/0.83  fof(f22,plain,(
% 3.18/0.83    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.18/0.83    inference(nnf_transformation,[],[f4])).
% 3.18/0.83  fof(f4,axiom,(
% 3.18/0.83    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.18/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 3.18/0.83  fof(f767,plain,(
% 3.18/0.83    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(sK1,sK2) | (spl5_2 | ~spl5_27 | ~spl5_30)),
% 3.18/0.83    inference(forward_demodulation,[],[f766,f495])).
% 3.18/0.83  fof(f495,plain,(
% 3.18/0.83    sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_30),
% 3.18/0.83    inference(avatar_component_clause,[],[f493])).
% 3.18/0.83  fof(f766,plain,(
% 3.18/0.83    r2_hidden(sK1,sK2) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | (spl5_2 | ~spl5_27 | ~spl5_30)),
% 3.18/0.83    inference(forward_demodulation,[],[f765,f495])).
% 3.18/0.83  fof(f765,plain,(
% 3.18/0.83    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | (spl5_2 | ~spl5_27)),
% 3.18/0.83    inference(subsumption_resolution,[],[f740,f424])).
% 3.18/0.83  fof(f424,plain,(
% 3.18/0.83    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl5_27),
% 3.18/0.83    inference(avatar_component_clause,[],[f422])).
% 3.18/0.83  fof(f740,plain,(
% 3.18/0.83    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_2),
% 3.18/0.83    inference(equality_resolution,[],[f199])).
% 3.18/0.83  fof(f199,plain,(
% 3.18/0.83    ( ! [X1] : (k2_enumset1(sK1,sK1,sK1,sK1) != X1 | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),sK2) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),X1)) ) | spl5_2),
% 3.18/0.83    inference(superposition,[],[f102,f66])).
% 3.18/0.83  fof(f66,plain,(
% 3.18/0.83    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 3.18/0.83    inference(definition_unfolding,[],[f47,f37])).
% 3.18/0.83  fof(f37,plain,(
% 3.18/0.83    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.18/0.83    inference(cnf_transformation,[],[f3])).
% 3.18/0.83  fof(f3,axiom,(
% 3.18/0.83    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.18/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.18/0.83  fof(f47,plain,(
% 3.18/0.83    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 3.18/0.83    inference(cnf_transformation,[],[f21])).
% 3.18/0.83  fof(f21,plain,(
% 3.18/0.83    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.18/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).
% 3.18/0.83  fof(f20,plain,(
% 3.18/0.83    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 3.18/0.83    introduced(choice_axiom,[])).
% 3.18/0.83  fof(f19,plain,(
% 3.18/0.83    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.18/0.83    inference(rectify,[],[f18])).
% 3.18/0.83  fof(f18,plain,(
% 3.18/0.83    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.18/0.83    inference(flattening,[],[f17])).
% 3.18/0.83  fof(f17,plain,(
% 3.18/0.83    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.18/0.83    inference(nnf_transformation,[],[f1])).
% 3.18/0.83  fof(f1,axiom,(
% 3.18/0.83    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.18/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 3.18/0.83  fof(f102,plain,(
% 3.18/0.83    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK1,sK1,sK1,sK1) | spl5_2),
% 3.18/0.83    inference(avatar_component_clause,[],[f100])).
% 3.18/0.83  fof(f764,plain,(
% 3.18/0.83    sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)),
% 3.18/0.83    introduced(theory_tautology_sat_conflict,[])).
% 3.18/0.83  fof(f763,plain,(
% 3.18/0.83    sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2)),
% 3.18/0.83    introduced(theory_tautology_sat_conflict,[])).
% 3.18/0.83  fof(f762,plain,(
% 3.18/0.83    sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))),
% 3.18/0.83    introduced(theory_tautology_sat_conflict,[])).
% 3.18/0.83  fof(f761,plain,(
% 3.18/0.83    spl5_16 | ~spl5_34),
% 3.18/0.83    inference(avatar_contradiction_clause,[],[f760])).
% 3.18/0.83  fof(f760,plain,(
% 3.18/0.83    $false | (spl5_16 | ~spl5_34)),
% 3.18/0.83    inference(subsumption_resolution,[],[f759,f90])).
% 3.18/0.83  fof(f759,plain,(
% 3.18/0.83    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | (spl5_16 | ~spl5_34)),
% 3.18/0.83    inference(forward_demodulation,[],[f326,f568])).
% 3.18/0.83  fof(f568,plain,(
% 3.18/0.83    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_34),
% 3.18/0.83    inference(avatar_component_clause,[],[f566])).
% 3.18/0.83  fof(f566,plain,(
% 3.18/0.83    spl5_34 <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 3.18/0.83  fof(f326,plain,(
% 3.18/0.83    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_16),
% 3.18/0.83    inference(avatar_component_clause,[],[f325])).
% 3.18/0.83  fof(f325,plain,(
% 3.18/0.83    spl5_16 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 3.18/0.83  fof(f735,plain,(
% 3.18/0.83    ~spl5_16 | ~spl5_25 | spl5_3 | spl5_17),
% 3.18/0.83    inference(avatar_split_clause,[],[f734,f329,f105,f407,f325])).
% 3.18/0.83  fof(f407,plain,(
% 3.18/0.83    spl5_25 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 3.18/0.83  fof(f105,plain,(
% 3.18/0.83    spl5_3 <=> k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 3.18/0.83  fof(f329,plain,(
% 3.18/0.83    spl5_17 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2)),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 3.18/0.83  fof(f734,plain,(
% 3.18/0.83    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | (spl5_3 | spl5_17)),
% 3.18/0.83    inference(subsumption_resolution,[],[f732,f331])).
% 3.18/0.83  fof(f331,plain,(
% 3.18/0.83    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2) | spl5_17),
% 3.18/0.83    inference(avatar_component_clause,[],[f329])).
% 3.18/0.83  fof(f732,plain,(
% 3.18/0.83    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_3),
% 3.18/0.83    inference(equality_resolution,[],[f198])).
% 3.18/0.83  fof(f198,plain,(
% 3.18/0.83    ( ! [X0] : (k2_enumset1(sK0,sK0,sK0,sK0) != X0 | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),sK2) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X0)) ) | spl5_3),
% 3.18/0.83    inference(superposition,[],[f107,f66])).
% 3.18/0.83  fof(f107,plain,(
% 3.18/0.83    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK0,sK0,sK0,sK0) | spl5_3),
% 3.18/0.83    inference(avatar_component_clause,[],[f105])).
% 3.18/0.83  fof(f689,plain,(
% 3.18/0.83    spl5_34 | ~spl5_16),
% 3.18/0.83    inference(avatar_split_clause,[],[f581,f325,f566])).
% 3.18/0.83  fof(f581,plain,(
% 3.18/0.83    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_16),
% 3.18/0.83    inference(duplicate_literal_removal,[],[f577])).
% 3.18/0.83  fof(f577,plain,(
% 3.18/0.83    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_16),
% 3.18/0.83    inference(resolution,[],[f327,f93])).
% 3.18/0.83  fof(f93,plain,(
% 3.18/0.83    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 3.18/0.83    inference(equality_resolution,[],[f77])).
% 3.18/0.83  fof(f77,plain,(
% 3.18/0.83    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.18/0.83    inference(definition_unfolding,[],[f48,f60])).
% 3.18/0.83  fof(f48,plain,(
% 3.18/0.83    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.18/0.83    inference(cnf_transformation,[],[f26])).
% 3.18/0.83  fof(f327,plain,(
% 3.18/0.83    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_16),
% 3.18/0.83    inference(avatar_component_clause,[],[f325])).
% 3.18/0.83  fof(f688,plain,(
% 3.18/0.83    spl5_30 | ~spl5_18),
% 3.18/0.83    inference(avatar_split_clause,[],[f491,f340,f493])).
% 3.18/0.83  fof(f340,plain,(
% 3.18/0.83    spl5_18 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 3.18/0.83  fof(f491,plain,(
% 3.18/0.83    sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_18),
% 3.18/0.83    inference(duplicate_literal_removal,[],[f487])).
% 3.18/0.83  fof(f487,plain,(
% 3.18/0.83    sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_18),
% 3.18/0.83    inference(resolution,[],[f342,f93])).
% 3.18/0.83  fof(f342,plain,(
% 3.18/0.83    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_18),
% 3.18/0.83    inference(avatar_component_clause,[],[f340])).
% 3.18/0.83  fof(f687,plain,(
% 3.18/0.83    spl5_30 | spl5_38 | ~spl5_27),
% 3.18/0.83    inference(avatar_split_clause,[],[f667,f422,f673,f493])).
% 3.18/0.83  fof(f673,plain,(
% 3.18/0.83    spl5_38 <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1))),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 3.18/0.83  fof(f667,plain,(
% 3.18/0.83    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_27),
% 3.18/0.83    inference(resolution,[],[f424,f93])).
% 3.18/0.83  fof(f686,plain,(
% 3.18/0.83    spl5_18 | ~spl5_19 | spl5_2),
% 3.18/0.83    inference(avatar_split_clause,[],[f549,f100,f344,f340])).
% 3.18/0.83  fof(f344,plain,(
% 3.18/0.83    spl5_19 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2)),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 3.18/0.83  fof(f549,plain,(
% 3.18/0.83    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_2),
% 3.18/0.83    inference(equality_resolution,[],[f126])).
% 3.18/0.83  fof(f126,plain,(
% 3.18/0.83    ( ! [X1] : (k2_enumset1(sK1,sK1,sK1,sK1) != X1 | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),X1)) ) | spl5_2),
% 3.18/0.83    inference(superposition,[],[f102,f67])).
% 3.18/0.83  fof(f67,plain,(
% 3.18/0.83    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 3.18/0.83    inference(definition_unfolding,[],[f46,f37])).
% 3.18/0.83  fof(f46,plain,(
% 3.18/0.83    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 3.18/0.83    inference(cnf_transformation,[],[f21])).
% 3.18/0.83  fof(f685,plain,(
% 3.18/0.83    sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2)),
% 3.18/0.83    introduced(theory_tautology_sat_conflict,[])).
% 3.18/0.83  fof(f677,plain,(
% 3.18/0.83    sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 3.18/0.83    introduced(theory_tautology_sat_conflict,[])).
% 3.18/0.83  fof(f569,plain,(
% 3.18/0.83    spl5_33 | spl5_34 | ~spl5_25),
% 3.18/0.83    inference(avatar_split_clause,[],[f557,f407,f566,f562])).
% 3.18/0.83  fof(f562,plain,(
% 3.18/0.83    spl5_33 <=> sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 3.18/0.83  fof(f557,plain,(
% 3.18/0.83    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_25),
% 3.18/0.83    inference(resolution,[],[f409,f93])).
% 3.18/0.83  fof(f409,plain,(
% 3.18/0.83    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl5_25),
% 3.18/0.83    inference(avatar_component_clause,[],[f407])).
% 3.18/0.83  fof(f541,plain,(
% 3.18/0.83    sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2)),
% 3.18/0.83    introduced(theory_tautology_sat_conflict,[])).
% 3.18/0.83  fof(f540,plain,(
% 3.18/0.83    sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) | r2_hidden(sK1,sK2)),
% 3.18/0.83    introduced(theory_tautology_sat_conflict,[])).
% 3.18/0.83  fof(f538,plain,(
% 3.18/0.83    spl5_31 | spl5_32 | ~spl5_20),
% 3.18/0.83    inference(avatar_split_clause,[],[f526,f354,f535,f531])).
% 3.18/0.83  fof(f531,plain,(
% 3.18/0.83    spl5_31 <=> sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 3.18/0.83  fof(f354,plain,(
% 3.18/0.83    spl5_20 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 3.18/0.83  fof(f526,plain,(
% 3.18/0.83    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl5_20),
% 3.18/0.83    inference(resolution,[],[f356,f93])).
% 3.18/0.83  fof(f356,plain,(
% 3.18/0.83    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl5_20),
% 3.18/0.83    inference(avatar_component_clause,[],[f354])).
% 3.18/0.83  fof(f529,plain,(
% 3.18/0.83    spl5_1 | ~spl5_20 | spl5_21),
% 3.18/0.83    inference(avatar_contradiction_clause,[],[f525])).
% 3.18/0.83  fof(f525,plain,(
% 3.18/0.83    $false | (spl5_1 | ~spl5_20 | spl5_21)),
% 3.18/0.83    inference(unit_resulting_resolution,[],[f360,f356,f97,f356,f66])).
% 3.18/0.83  fof(f97,plain,(
% 3.18/0.83    k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) | spl5_1),
% 3.18/0.83    inference(avatar_component_clause,[],[f95])).
% 3.18/0.83  fof(f95,plain,(
% 3.18/0.83    spl5_1 <=> k2_enumset1(sK0,sK0,sK0,sK1) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 3.18/0.83  fof(f360,plain,(
% 3.18/0.83    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) | spl5_21),
% 3.18/0.83    inference(avatar_component_clause,[],[f358])).
% 3.18/0.83  fof(f429,plain,(
% 3.18/0.83    spl5_20 | spl5_1),
% 3.18/0.83    inference(avatar_split_clause,[],[f428,f95,f354])).
% 3.18/0.83  fof(f428,plain,(
% 3.18/0.83    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | spl5_1),
% 3.18/0.83    inference(duplicate_literal_removal,[],[f427])).
% 3.18/0.83  fof(f427,plain,(
% 3.18/0.83    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | spl5_1),
% 3.18/0.83    inference(equality_resolution,[],[f138])).
% 3.18/0.83  fof(f138,plain,(
% 3.18/0.83    ( ! [X2] : (k2_enumset1(sK0,sK0,sK0,sK1) != X2 | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X2),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X2),X2)) ) | spl5_1),
% 3.18/0.83    inference(superposition,[],[f97,f68])).
% 3.18/0.83  fof(f68,plain,(
% 3.18/0.83    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 3.18/0.83    inference(definition_unfolding,[],[f45,f37])).
% 3.18/0.83  fof(f45,plain,(
% 3.18/0.83    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 3.18/0.83    inference(cnf_transformation,[],[f21])).
% 3.18/0.83  fof(f425,plain,(
% 3.18/0.83    spl5_18 | spl5_27 | spl5_2),
% 3.18/0.83    inference(avatar_split_clause,[],[f419,f100,f422,f340])).
% 3.18/0.83  fof(f419,plain,(
% 3.18/0.83    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_2),
% 3.18/0.83    inference(equality_resolution,[],[f137])).
% 3.18/0.83  fof(f137,plain,(
% 3.18/0.83    ( ! [X1] : (k2_enumset1(sK1,sK1,sK1,sK1) != X1 | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),X1)) ) | spl5_2),
% 3.18/0.83    inference(superposition,[],[f102,f68])).
% 3.18/0.83  fof(f410,plain,(
% 3.18/0.83    spl5_16 | spl5_25 | spl5_3),
% 3.18/0.83    inference(avatar_split_clause,[],[f404,f105,f407,f325])).
% 3.18/0.83  fof(f404,plain,(
% 3.18/0.83    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_3),
% 3.18/0.83    inference(equality_resolution,[],[f136])).
% 3.18/0.83  fof(f136,plain,(
% 3.18/0.83    ( ! [X0] : (k2_enumset1(sK0,sK0,sK0,sK0) != X0 | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X0)) ) | spl5_3),
% 3.18/0.83    inference(superposition,[],[f107,f68])).
% 3.18/0.83  fof(f392,plain,(
% 3.18/0.83    spl5_23 | spl5_24 | ~spl5_22),
% 3.18/0.83    inference(avatar_split_clause,[],[f382,f366,f389,f385])).
% 3.18/0.83  fof(f389,plain,(
% 3.18/0.83    spl5_24 <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0)),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 3.18/0.83  fof(f366,plain,(
% 3.18/0.83    spl5_22 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1))),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 3.18/0.83  fof(f382,plain,(
% 3.18/0.83    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0) | ~spl5_22),
% 3.18/0.83    inference(resolution,[],[f368,f93])).
% 3.18/0.83  fof(f368,plain,(
% 3.18/0.83    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl5_22),
% 3.18/0.83    inference(avatar_component_clause,[],[f366])).
% 3.18/0.83  fof(f374,plain,(
% 3.18/0.83    spl5_22 | spl5_4 | spl5_5),
% 3.18/0.83    inference(avatar_split_clause,[],[f364,f148,f110,f366])).
% 3.18/0.83  fof(f110,plain,(
% 3.18/0.83    spl5_4 <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 3.18/0.83  fof(f148,plain,(
% 3.18/0.83    spl5_5 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)),
% 3.18/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 3.18/0.83  fof(f364,plain,(
% 3.18/0.83    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) | (spl5_4 | spl5_5)),
% 3.18/0.83    inference(subsumption_resolution,[],[f363,f149])).
% 3.18/0.83  fof(f149,plain,(
% 3.18/0.83    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | spl5_5),
% 3.18/0.83    inference(avatar_component_clause,[],[f148])).
% 3.18/0.83  fof(f363,plain,(
% 3.18/0.83    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | spl5_4),
% 3.18/0.83    inference(equality_resolution,[],[f139])).
% 3.18/0.83  fof(f139,plain,(
% 3.18/0.83    ( ! [X3] : (k1_xboole_0 != X3 | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X3),k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X3),X3)) ) | spl5_4),
% 3.18/0.83    inference(superposition,[],[f112,f68])).
% 3.18/0.83  fof(f112,plain,(
% 3.18/0.83    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) | spl5_4),
% 3.18/0.83    inference(avatar_component_clause,[],[f110])).
% 3.18/0.83  fof(f373,plain,(
% 3.18/0.83    ~spl5_5),
% 3.18/0.83    inference(avatar_contradiction_clause,[],[f372])).
% 3.18/0.83  fof(f372,plain,(
% 3.18/0.83    $false | ~spl5_5),
% 3.18/0.83    inference(subsumption_resolution,[],[f150,f168])).
% 3.18/0.83  fof(f168,plain,(
% 3.18/0.83    ( ! [X24,X23,X25,X22] : (~r2_hidden(X25,k1_xboole_0) | ~r2_hidden(X25,X24) | ~r2_hidden(X23,X24) | ~r2_hidden(X22,X24)) )),
% 3.18/0.83    inference(superposition,[],[f87,f81])).
% 3.18/0.83  fof(f81,plain,(
% 3.18/0.83    ( ! [X2,X0,X1] : (k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X1),k3_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.18/0.83    inference(definition_unfolding,[],[f59,f37,f60])).
% 3.18/0.83  fof(f59,plain,(
% 3.18/0.83    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.18/0.83    inference(cnf_transformation,[],[f30])).
% 3.18/0.83  fof(f30,plain,(
% 3.18/0.83    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0))),
% 3.18/0.83    inference(flattening,[],[f29])).
% 3.18/0.83  fof(f29,plain,(
% 3.18/0.83    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0))),
% 3.18/0.83    inference(nnf_transformation,[],[f9])).
% 3.18/0.83  fof(f9,axiom,(
% 3.18/0.83    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.18/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 3.18/0.83  fof(f87,plain,(
% 3.18/0.83    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 3.18/0.83    inference(equality_resolution,[],[f70])).
% 3.18/0.83  fof(f70,plain,(
% 3.18/0.83    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.18/0.83    inference(definition_unfolding,[],[f43,f37])).
% 3.18/0.83  fof(f43,plain,(
% 3.18/0.83    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.18/0.83    inference(cnf_transformation,[],[f21])).
% 3.18/0.83  fof(f150,plain,(
% 3.18/0.83    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | ~spl5_5),
% 3.18/0.83    inference(avatar_component_clause,[],[f148])).
% 3.18/0.83  fof(f332,plain,(
% 3.18/0.83    spl5_16 | ~spl5_17 | spl5_3),
% 3.18/0.83    inference(avatar_split_clause,[],[f322,f105,f329,f325])).
% 3.18/0.83  fof(f322,plain,(
% 3.18/0.83    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_3),
% 3.18/0.83    inference(equality_resolution,[],[f125])).
% 3.18/0.83  fof(f125,plain,(
% 3.18/0.83    ( ! [X0] : (k2_enumset1(sK0,sK0,sK0,sK0) != X0 | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X0)) ) | spl5_3),
% 3.18/0.83    inference(superposition,[],[f107,f67])).
% 3.18/0.83  fof(f193,plain,(
% 3.18/0.83    ~spl5_7 | ~spl5_8 | spl5_4),
% 3.18/0.83    inference(avatar_split_clause,[],[f169,f110,f175,f171])).
% 3.18/0.83  fof(f169,plain,(
% 3.18/0.83    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | spl5_4),
% 3.18/0.83    inference(trivial_inequality_removal,[],[f161])).
% 3.18/0.83  fof(f161,plain,(
% 3.18/0.83    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | spl5_4),
% 3.18/0.83    inference(superposition,[],[f112,f81])).
% 3.18/0.83  fof(f155,plain,(
% 3.18/0.83    spl5_5 | ~spl5_6 | spl5_4),
% 3.18/0.83    inference(avatar_split_clause,[],[f146,f110,f152,f148])).
% 3.18/0.83  fof(f146,plain,(
% 3.18/0.83    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | spl5_4),
% 3.18/0.83    inference(equality_resolution,[],[f128])).
% 3.18/0.83  fof(f128,plain,(
% 3.18/0.83    ( ! [X3] : (k1_xboole_0 != X3 | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X3),sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X3),X3)) ) | spl5_4),
% 3.18/0.83    inference(superposition,[],[f112,f67])).
% 3.18/0.83  fof(f113,plain,(
% 3.18/0.83    ~spl5_4),
% 3.18/0.83    inference(avatar_split_clause,[],[f65,f110])).
% 3.18/0.83  fof(f65,plain,(
% 3.18/0.83    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),
% 3.18/0.83    inference(definition_unfolding,[],[f31,f37,f60])).
% 3.18/0.83  fof(f31,plain,(
% 3.18/0.83    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 3.18/0.83    inference(cnf_transformation,[],[f14])).
% 3.18/0.83  fof(f14,plain,(
% 3.18/0.83    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 3.18/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 3.18/0.83  fof(f13,plain,(
% 3.18/0.83    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0) => (k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 3.18/0.83    introduced(choice_axiom,[])).
% 3.18/0.83  fof(f12,plain,(
% 3.18/0.83    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0)),
% 3.18/0.83    inference(ennf_transformation,[],[f11])).
% 3.18/0.83  fof(f11,negated_conjecture,(
% 3.18/0.83    ~! [X0,X1,X2] : ~(k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0)),
% 3.18/0.83    inference(negated_conjecture,[],[f10])).
% 3.18/0.83  fof(f10,conjecture,(
% 3.18/0.83    ! [X0,X1,X2] : ~(k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0)),
% 3.18/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_zfmisc_1)).
% 3.18/0.83  fof(f108,plain,(
% 3.18/0.83    ~spl5_3),
% 3.18/0.83    inference(avatar_split_clause,[],[f64,f105])).
% 3.18/0.83  fof(f64,plain,(
% 3.18/0.83    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK0,sK0,sK0,sK0)),
% 3.18/0.83    inference(definition_unfolding,[],[f32,f37,f60,f61])).
% 3.18/0.83  fof(f61,plain,(
% 3.18/0.83    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.18/0.83    inference(definition_unfolding,[],[f35,f60])).
% 3.18/0.83  fof(f35,plain,(
% 3.18/0.83    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.18/0.83    inference(cnf_transformation,[],[f5])).
% 3.18/0.83  fof(f5,axiom,(
% 3.18/0.83    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.18/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 3.18/0.83  fof(f32,plain,(
% 3.18/0.83    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)),
% 3.18/0.83    inference(cnf_transformation,[],[f14])).
% 3.18/0.83  fof(f103,plain,(
% 3.18/0.83    ~spl5_2),
% 3.18/0.83    inference(avatar_split_clause,[],[f63,f100])).
% 3.18/0.83  fof(f63,plain,(
% 3.18/0.83    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)) != k2_enumset1(sK1,sK1,sK1,sK1)),
% 3.18/0.83    inference(definition_unfolding,[],[f33,f37,f60,f61])).
% 3.18/0.83  fof(f33,plain,(
% 3.18/0.83    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)),
% 3.18/0.83    inference(cnf_transformation,[],[f14])).
% 3.18/0.83  fof(f98,plain,(
% 3.18/0.83    ~spl5_1),
% 3.18/0.83    inference(avatar_split_clause,[],[f62,f95])).
% 3.18/0.83  fof(f62,plain,(
% 3.18/0.83    k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2))),
% 3.18/0.83    inference(definition_unfolding,[],[f34,f60,f37,f60])).
% 3.18/0.83  fof(f34,plain,(
% 3.18/0.83    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 3.18/0.83    inference(cnf_transformation,[],[f14])).
% 3.18/0.83  % SZS output end Proof for theBenchmark
% 3.18/0.83  % (21239)------------------------------
% 3.18/0.83  % (21239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.18/0.83  % (21239)Termination reason: Refutation
% 3.18/0.83  
% 3.18/0.83  % (21239)Memory used [KB]: 11257
% 3.18/0.83  % (21239)Time elapsed: 0.258 s
% 3.18/0.83  % (21239)------------------------------
% 3.18/0.83  % (21239)------------------------------
% 3.18/0.84  % (21207)Success in time 0.464 s
%------------------------------------------------------------------------------
