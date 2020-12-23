%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 763 expanded)
%              Number of leaves         :   20 ( 230 expanded)
%              Depth                    :   16
%              Number of atoms          :  333 (2406 expanded)
%              Number of equality atoms :  205 (1750 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f309,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f185,f239,f279,f308])).

fof(f308,plain,
    ( ~ spl5_1
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f307])).

fof(f307,plain,
    ( $false
    | ~ spl5_1
    | spl5_4 ),
    inference(subsumption_resolution,[],[f306,f299])).

fof(f299,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl5_1
    | spl5_4 ),
    inference(forward_demodulation,[],[f129,f295])).

fof(f295,plain,
    ( sK1 = sK3
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f293,f41])).

fof(f41,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f293,plain,
    ( sK0 = sK3
    | sK1 = sK3
    | ~ spl5_1 ),
    inference(resolution,[],[f290,f109])).

fof(f109,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_enumset1(X0,X0,X0,X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f55,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f69,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
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

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f290,plain,
    ( r2_hidden(sK3,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_1 ),
    inference(superposition,[],[f106,f118])).

fof(f118,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl5_1
  <=> k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f106,plain,(
    ! [X4,X0] : r2_hidden(X4,k4_enumset1(X0,X0,X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k4_enumset1(X0,X0,X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f57,f74])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f129,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl5_4
  <=> k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f306,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f297,f302])).

fof(f302,plain,
    ( sK1 = sK2
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f300,f40])).

fof(f40,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f300,plain,
    ( sK0 = sK2
    | sK1 = sK2
    | ~ spl5_1 ),
    inference(resolution,[],[f291,f109])).

fof(f291,plain,
    ( r2_hidden(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_1 ),
    inference(superposition,[],[f108,f118])).

fof(f108,plain,(
    ! [X4,X1] : r2_hidden(X4,k4_enumset1(X4,X4,X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k4_enumset1(X4,X4,X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f56,f74])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f297,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK1)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f118,f295])).

fof(f279,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f273,f265])).

fof(f265,plain,
    ( sK0 != sK1
    | ~ spl5_4 ),
    inference(superposition,[],[f41,f260])).

fof(f260,plain,
    ( sK1 = sK3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f258,f41])).

fof(f258,plain,
    ( sK0 = sK3
    | sK1 = sK3
    | ~ spl5_4 ),
    inference(resolution,[],[f248,f109])).

fof(f248,plain,
    ( r2_hidden(sK3,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_4 ),
    inference(superposition,[],[f106,f130])).

fof(f130,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f273,plain,
    ( sK0 = sK1
    | ~ spl5_4 ),
    inference(resolution,[],[f271,f108])).

fof(f271,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X1 )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f256,f260])).

fof(f256,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))
        | sK3 = X1 )
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f250])).

fof(f250,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))
        | sK3 = X1
        | sK3 = X1 )
    | ~ spl5_4 ),
    inference(superposition,[],[f109,f130])).

fof(f239,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f233,f211])).

fof(f211,plain,
    ( sK0 != sK1
    | ~ spl5_3 ),
    inference(superposition,[],[f40,f206])).

fof(f206,plain,
    ( sK1 = sK2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f204,f40])).

fof(f204,plain,
    ( sK0 = sK2
    | sK1 = sK2
    | ~ spl5_3 ),
    inference(resolution,[],[f194,f109])).

fof(f194,plain,
    ( r2_hidden(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_3 ),
    inference(superposition,[],[f106,f126])).

fof(f126,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl5_3
  <=> k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f233,plain,
    ( sK0 = sK1
    | ~ spl5_3 ),
    inference(resolution,[],[f216,f108])).

fof(f216,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X1 )
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f202,f206])).

fof(f202,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))
        | sK2 = X1 )
    | ~ spl5_3 ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))
        | sK2 = X1
        | sK2 = X1 )
    | ~ spl5_3 ),
    inference(superposition,[],[f109,f126])).

fof(f185,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f170,f177])).

fof(f177,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f133,f144])).

fof(f144,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f132,f67])).

fof(f67,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f132,plain,
    ( k4_xboole_0(k1_xboole_0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f113,f122])).

fof(f122,plain,
    ( k1_xboole_0 = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl5_2
  <=> k1_xboole_0 = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f113,plain,(
    k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f76,f112])).

fof(f112,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))) ),
    inference(resolution,[],[f77,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f50,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f77,plain,(
    r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f39,f74,f74])).

fof(f39,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f68,f63])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f133,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)))
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f112,f122])).

fof(f170,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_2 ),
    inference(superposition,[],[f110,f152])).

fof(f152,plain,
    ( k1_xboole_0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f151,f97])).

fof(f97,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f64,f63])).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f151,plain,
    ( k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0))
    | ~ spl5_2 ),
    inference(resolution,[],[f137,f86])).

fof(f137,plain,
    ( r1_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)
    | ~ spl5_2 ),
    inference(superposition,[],[f101,f122])).

fof(f101,plain,(
    ! [X2,X1] : r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2))
      | k4_enumset1(X2,X2,X2,X2,X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f47,f74,f75])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f62,f74])).

fof(f62,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f110,plain,(
    ! [X1] : k4_enumset1(X1,X1,X1,X1,X1,X1) != k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_enumset1(X0,X0,X0,X0,X0,X0) != k4_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f65,f75,f75,f75])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f131,plain,
    ( spl5_1
    | spl5_2
    | spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f111,f128,f124,f120,f116])).

fof(f111,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)
    | k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)
    | k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(resolution,[],[f77,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2))
      | k4_enumset1(X2,X2,X2,X2,X2,X2) = X0
      | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | k4_enumset1(X1,X1,X1,X1,X1,X2) = X0 ) ),
    inference(definition_unfolding,[],[f44,f74,f75,f75,f74])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:52:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (25393)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (25417)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (25409)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.51  % (25395)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (25396)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (25414)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (25406)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (25408)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (25392)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (25392)Refutation not found, incomplete strategy% (25392)------------------------------
% 0.21/0.53  % (25392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (25397)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (25398)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (25392)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (25392)Memory used [KB]: 1663
% 0.21/0.53  % (25392)Time elapsed: 0.106 s
% 0.21/0.53  % (25392)------------------------------
% 0.21/0.53  % (25392)------------------------------
% 0.21/0.53  % (25400)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (25416)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (25403)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (25391)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (25413)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (25394)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (25404)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (25405)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (25401)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (25420)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (25411)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (25403)Refutation not found, incomplete strategy% (25403)------------------------------
% 0.21/0.55  % (25403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (25399)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (25412)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (25415)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (25410)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (25419)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (25407)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (25402)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (25407)Refutation not found, incomplete strategy% (25407)------------------------------
% 0.21/0.55  % (25407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (25407)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (25407)Memory used [KB]: 10618
% 0.21/0.55  % (25407)Time elapsed: 0.140 s
% 0.21/0.55  % (25407)------------------------------
% 0.21/0.55  % (25407)------------------------------
% 0.21/0.55  % (25415)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f309,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f131,f185,f239,f279,f308])).
% 0.21/0.55  fof(f308,plain,(
% 0.21/0.55    ~spl5_1 | spl5_4),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f307])).
% 0.21/0.55  fof(f307,plain,(
% 0.21/0.55    $false | (~spl5_1 | spl5_4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f306,f299])).
% 0.21/0.55  fof(f299,plain,(
% 0.21/0.55    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | (~spl5_1 | spl5_4)),
% 0.21/0.55    inference(forward_demodulation,[],[f129,f295])).
% 0.21/0.55  fof(f295,plain,(
% 0.21/0.55    sK1 = sK3 | ~spl5_1),
% 0.21/0.55    inference(subsumption_resolution,[],[f293,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    sK0 != sK3),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.21/0.55    inference(ennf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.21/0.55    inference(negated_conjecture,[],[f20])).
% 0.21/0.55  fof(f20,conjecture,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 0.21/0.55  fof(f293,plain,(
% 0.21/0.55    sK0 = sK3 | sK1 = sK3 | ~spl5_1),
% 0.21/0.55    inference(resolution,[],[f290,f109])).
% 0.21/0.55  fof(f109,plain,(
% 0.21/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_enumset1(X0,X0,X0,X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.21/0.55    inference(equality_resolution,[],[f96])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2) )),
% 0.21/0.55    inference(definition_unfolding,[],[f55,f74])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f61,f73])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f69,f72])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f70,f71])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.55    inference(rectify,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.55    inference(flattening,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.55    inference(nnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.55  fof(f290,plain,(
% 0.21/0.55    r2_hidden(sK3,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl5_1),
% 0.21/0.55    inference(superposition,[],[f106,f118])).
% 0.21/0.55  fof(f118,plain,(
% 0.21/0.55    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3) | ~spl5_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f116])).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    spl5_1 <=> k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    ( ! [X4,X0] : (r2_hidden(X4,k4_enumset1(X0,X0,X0,X0,X0,X4))) )),
% 0.21/0.55    inference(equality_resolution,[],[f105])).
% 0.21/0.55  fof(f105,plain,(
% 0.21/0.55    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k4_enumset1(X0,X0,X0,X0,X0,X4) != X2) )),
% 0.21/0.55    inference(equality_resolution,[],[f94])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2) )),
% 0.21/0.55    inference(definition_unfolding,[],[f57,f74])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) | spl5_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f128])).
% 0.21/0.55  fof(f128,plain,(
% 0.21/0.55    spl5_4 <=> k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.55  fof(f306,plain,(
% 0.21/0.55    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | ~spl5_1),
% 0.21/0.55    inference(forward_demodulation,[],[f297,f302])).
% 0.21/0.55  fof(f302,plain,(
% 0.21/0.55    sK1 = sK2 | ~spl5_1),
% 0.21/0.55    inference(subsumption_resolution,[],[f300,f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    sK0 != sK2),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f300,plain,(
% 0.21/0.55    sK0 = sK2 | sK1 = sK2 | ~spl5_1),
% 0.21/0.55    inference(resolution,[],[f291,f109])).
% 0.21/0.55  fof(f291,plain,(
% 0.21/0.55    r2_hidden(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl5_1),
% 0.21/0.55    inference(superposition,[],[f108,f118])).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    ( ! [X4,X1] : (r2_hidden(X4,k4_enumset1(X4,X4,X4,X4,X4,X1))) )),
% 0.21/0.55    inference(equality_resolution,[],[f107])).
% 0.21/0.55  fof(f107,plain,(
% 0.21/0.55    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k4_enumset1(X4,X4,X4,X4,X4,X1) != X2) )),
% 0.21/0.55    inference(equality_resolution,[],[f95])).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k4_enumset1(X0,X0,X0,X0,X0,X1) != X2) )),
% 0.21/0.55    inference(definition_unfolding,[],[f56,f74])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f297,plain,(
% 0.21/0.55    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK1) | ~spl5_1),
% 0.21/0.55    inference(backward_demodulation,[],[f118,f295])).
% 0.21/0.55  fof(f279,plain,(
% 0.21/0.55    ~spl5_4),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f278])).
% 0.21/0.55  fof(f278,plain,(
% 0.21/0.55    $false | ~spl5_4),
% 0.21/0.55    inference(subsumption_resolution,[],[f273,f265])).
% 0.21/0.55  fof(f265,plain,(
% 0.21/0.55    sK0 != sK1 | ~spl5_4),
% 0.21/0.55    inference(superposition,[],[f41,f260])).
% 0.21/0.55  fof(f260,plain,(
% 0.21/0.55    sK1 = sK3 | ~spl5_4),
% 0.21/0.55    inference(subsumption_resolution,[],[f258,f41])).
% 0.21/0.55  fof(f258,plain,(
% 0.21/0.55    sK0 = sK3 | sK1 = sK3 | ~spl5_4),
% 0.21/0.55    inference(resolution,[],[f248,f109])).
% 0.21/0.55  fof(f248,plain,(
% 0.21/0.55    r2_hidden(sK3,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl5_4),
% 0.21/0.55    inference(superposition,[],[f106,f130])).
% 0.21/0.55  fof(f130,plain,(
% 0.21/0.55    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) | ~spl5_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f128])).
% 0.21/0.55  fof(f273,plain,(
% 0.21/0.55    sK0 = sK1 | ~spl5_4),
% 0.21/0.55    inference(resolution,[],[f271,f108])).
% 0.21/0.55  fof(f271,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X1) ) | ~spl5_4),
% 0.21/0.55    inference(forward_demodulation,[],[f256,f260])).
% 0.21/0.55  fof(f256,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) | sK3 = X1) ) | ~spl5_4),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f250])).
% 0.21/0.55  fof(f250,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) | sK3 = X1 | sK3 = X1) ) | ~spl5_4),
% 0.21/0.55    inference(superposition,[],[f109,f130])).
% 0.21/0.55  fof(f239,plain,(
% 0.21/0.55    ~spl5_3),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f238])).
% 0.21/0.55  fof(f238,plain,(
% 0.21/0.55    $false | ~spl5_3),
% 0.21/0.55    inference(subsumption_resolution,[],[f233,f211])).
% 0.21/0.55  fof(f211,plain,(
% 0.21/0.55    sK0 != sK1 | ~spl5_3),
% 0.21/0.55    inference(superposition,[],[f40,f206])).
% 0.21/0.55  fof(f206,plain,(
% 0.21/0.55    sK1 = sK2 | ~spl5_3),
% 0.21/0.55    inference(subsumption_resolution,[],[f204,f40])).
% 0.21/0.55  fof(f204,plain,(
% 0.21/0.55    sK0 = sK2 | sK1 = sK2 | ~spl5_3),
% 0.21/0.55    inference(resolution,[],[f194,f109])).
% 0.21/0.55  fof(f194,plain,(
% 0.21/0.55    r2_hidden(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl5_3),
% 0.21/0.55    inference(superposition,[],[f106,f126])).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) | ~spl5_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f124])).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    spl5_3 <=> k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.55  fof(f233,plain,(
% 0.21/0.55    sK0 = sK1 | ~spl5_3),
% 0.21/0.55    inference(resolution,[],[f216,f108])).
% 0.21/0.55  fof(f216,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X1) ) | ~spl5_3),
% 0.21/0.55    inference(forward_demodulation,[],[f202,f206])).
% 0.21/0.55  fof(f202,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) | sK2 = X1) ) | ~spl5_3),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f196])).
% 0.21/0.55  fof(f196,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) | sK2 = X1 | sK2 = X1) ) | ~spl5_3),
% 0.21/0.55    inference(superposition,[],[f109,f126])).
% 0.21/0.55  fof(f185,plain,(
% 0.21/0.55    ~spl5_2),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f184])).
% 0.21/0.55  fof(f184,plain,(
% 0.21/0.55    $false | ~spl5_2),
% 0.21/0.55    inference(subsumption_resolution,[],[f170,f177])).
% 0.21/0.55  fof(f177,plain,(
% 0.21/0.55    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_2),
% 0.21/0.55    inference(backward_demodulation,[],[f133,f144])).
% 0.21/0.55  fof(f144,plain,(
% 0.21/0.55    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)) | ~spl5_2),
% 0.21/0.55    inference(forward_demodulation,[],[f132,f67])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.55  fof(f132,plain,(
% 0.21/0.55    k4_xboole_0(k1_xboole_0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_2),
% 0.21/0.55    inference(backward_demodulation,[],[f113,f122])).
% 0.21/0.55  fof(f122,plain,(
% 0.21/0.55    k1_xboole_0 = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) | ~spl5_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f120])).
% 0.21/0.55  fof(f120,plain,(
% 0.21/0.55    spl5_2 <=> k1_xboole_0 = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),
% 0.21/0.55    inference(superposition,[],[f76,f112])).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)))),
% 0.21/0.55    inference(resolution,[],[f77,f86])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.55    inference(definition_unfolding,[],[f50,f63])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))),
% 0.21/0.55    inference(definition_unfolding,[],[f39,f74,f74])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f68,f63])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3))) | ~spl5_2),
% 0.21/0.55    inference(backward_demodulation,[],[f112,f122])).
% 0.21/0.55  fof(f170,plain,(
% 0.21/0.55    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_2),
% 0.21/0.55    inference(superposition,[],[f110,f152])).
% 0.21/0.55  fof(f152,plain,(
% 0.21/0.55    k1_xboole_0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | ~spl5_2),
% 0.21/0.55    inference(forward_demodulation,[],[f151,f97])).
% 0.21/0.55  fof(f97,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f64,f63])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.55  fof(f151,plain,(
% 0.21/0.55    k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)) | ~spl5_2),
% 0.21/0.55    inference(resolution,[],[f137,f86])).
% 0.21/0.55  fof(f137,plain,(
% 0.21/0.55    r1_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) | ~spl5_2),
% 0.21/0.55    inference(superposition,[],[f101,f122])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    ( ! [X2,X1] : (r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X1,X1,X1,X1,X1,X2))) )),
% 0.21/0.55    inference(equality_resolution,[],[f81])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2)) | k4_enumset1(X2,X2,X2,X2,X2,X2) != X0) )),
% 0.21/0.55    inference(definition_unfolding,[],[f47,f74,f75])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f62,f74])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.21/0.55    inference(flattening,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.21/0.55    inference(nnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.21/0.55  fof(f110,plain,(
% 0.21/0.55    ( ! [X1] : (k4_enumset1(X1,X1,X1,X1,X1,X1) != k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1))) )),
% 0.21/0.55    inference(equality_resolution,[],[f99])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    ( ! [X0,X1] : (X0 != X1 | k4_enumset1(X0,X0,X0,X0,X0,X0) != k4_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X1,X1,X1,X1,X1,X1))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f65,f75,f75,f75])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.21/0.55    inference(nnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,axiom,(
% 0.21/0.55    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.55  fof(f131,plain,(
% 0.21/0.55    spl5_1 | spl5_2 | spl5_3 | spl5_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f111,f128,f124,f120,f116])).
% 0.21/0.55  fof(f111,plain,(
% 0.21/0.55    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) | k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) | k1_xboole_0 = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) | k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK3)),
% 0.21/0.55    inference(resolution,[],[f77,f84])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2)) | k4_enumset1(X2,X2,X2,X2,X2,X2) = X0 | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | k4_enumset1(X1,X1,X1,X1,X1,X2) = X0) )),
% 0.21/0.55    inference(definition_unfolding,[],[f44,f74,f75,f75,f74])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (25415)------------------------------
% 0.21/0.55  % (25415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (25415)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (25415)Memory used [KB]: 10746
% 0.21/0.55  % (25415)Time elapsed: 0.130 s
% 0.21/0.55  % (25415)------------------------------
% 0.21/0.55  % (25415)------------------------------
% 0.21/0.55  % (25403)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (25403)Memory used [KB]: 10618
% 0.21/0.55  % (25403)Time elapsed: 0.134 s
% 0.21/0.55  % (25403)------------------------------
% 0.21/0.55  % (25403)------------------------------
% 0.21/0.55  % (25390)Success in time 0.19 s
%------------------------------------------------------------------------------
