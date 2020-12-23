%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:30 EST 2020

% Result     : Theorem 7.26s
% Output     : Refutation 7.26s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 286 expanded)
%              Number of leaves         :   27 (  90 expanded)
%              Depth                    :   19
%              Number of atoms          :  526 (1341 expanded)
%              Number of equality atoms :  254 ( 767 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7245,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f144,f149,f162,f666,f983,f2899,f5646,f5705,f5747,f5801,f7244])).

fof(f7244,plain,
    ( ~ spl14_3
    | ~ spl14_18
    | spl14_168
    | ~ spl14_169 ),
    inference(avatar_contradiction_clause,[],[f7243])).

fof(f7243,plain,
    ( $false
    | ~ spl14_3
    | ~ spl14_18
    | spl14_168
    | ~ spl14_169 ),
    inference(subsumption_resolution,[],[f7242,f5644])).

fof(f5644,plain,
    ( k1_xboole_0 != k2_tarski(sK0,sK0)
    | spl14_168 ),
    inference(avatar_component_clause,[],[f5643])).

fof(f5643,plain,
    ( spl14_168
  <=> k1_xboole_0 = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_168])])).

fof(f7242,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK0)
    | ~ spl14_3
    | ~ spl14_18
    | ~ spl14_169 ),
    inference(equality_resolution,[],[f7202])).

fof(f7202,plain,
    ( ! [X36] :
        ( sK0 != X36
        | k1_xboole_0 = k2_tarski(X36,sK0) )
    | ~ spl14_3
    | ~ spl14_18
    | ~ spl14_169 ),
    inference(subsumption_resolution,[],[f7188,f130])).

fof(f130,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f129])).

fof(f129,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK12(X0,X1,X2) != X1
              & sK12(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK12(X0,X1,X2),X2) )
          & ( sK12(X0,X1,X2) = X1
            | sK12(X0,X1,X2) = X0
            | r2_hidden(sK12(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK12(X0,X1,X2) != X1
            & sK12(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK12(X0,X1,X2),X2) )
        & ( sK12(X0,X1,X2) = X1
          | sK12(X0,X1,X2) = X0
          | r2_hidden(sK12(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
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

fof(f7188,plain,
    ( ! [X36] :
        ( sK0 != X36
        | k1_xboole_0 = k2_tarski(X36,sK0)
        | ~ r2_hidden(sK0,k2_tarski(X36,sK0)) )
    | ~ spl14_3
    | ~ spl14_18
    | ~ spl14_169 ),
    inference(duplicate_literal_removal,[],[f7187])).

fof(f7187,plain,
    ( ! [X36] :
        ( sK0 != X36
        | k1_xboole_0 = k2_tarski(X36,sK0)
        | ~ r2_hidden(sK0,k2_tarski(X36,sK0))
        | k1_xboole_0 = k2_tarski(X36,sK0) )
    | ~ spl14_3
    | ~ spl14_18
    | ~ spl14_169 ),
    inference(superposition,[],[f5717,f6799])).

fof(f6799,plain,
    ( ! [X0] :
        ( sK11(k2_tarski(X0,sK0)) = X0
        | k1_xboole_0 = k2_tarski(X0,sK0) )
    | ~ spl14_3
    | ~ spl14_18 ),
    inference(subsumption_resolution,[],[f6798,f130])).

fof(f6798,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k2_tarski(X0,sK0))
        | k1_xboole_0 = k2_tarski(X0,sK0)
        | sK11(k2_tarski(X0,sK0)) = X0 )
    | ~ spl14_3
    | ~ spl14_18 ),
    inference(equality_resolution,[],[f5761])).

fof(f5761,plain,
    ( ! [X0,X1] :
        ( sK0 != X1
        | ~ r2_hidden(sK0,k2_tarski(X0,X1))
        | k2_tarski(X0,X1) = k1_xboole_0
        | sK11(k2_tarski(X0,X1)) = X0 )
    | ~ spl14_3
    | ~ spl14_18 ),
    inference(backward_demodulation,[],[f4285,f355])).

fof(f355,plain,
    ( sK0 = sK1
    | ~ spl14_18 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl14_18
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).

fof(f4285,plain,
    ( ! [X0,X1] :
        ( sK0 != X1
        | ~ r2_hidden(sK1,k2_tarski(X0,X1))
        | k2_tarski(X0,X1) = k1_xboole_0
        | sK11(k2_tarski(X0,X1)) = X0 )
    | ~ spl14_3 ),
    inference(duplicate_literal_removal,[],[f4284])).

fof(f4284,plain,
    ( ! [X0,X1] :
        ( sK0 != X1
        | ~ r2_hidden(sK1,k2_tarski(X0,X1))
        | k2_tarski(X0,X1) = k1_xboole_0
        | sK11(k2_tarski(X0,X1)) = X0
        | k2_tarski(X0,X1) = k1_xboole_0 )
    | ~ spl14_3 ),
    inference(superposition,[],[f605,f310])).

fof(f310,plain,(
    ! [X12,X13] :
      ( sK11(k2_tarski(X12,X13)) = X13
      | sK11(k2_tarski(X12,X13)) = X12
      | k1_xboole_0 = k2_tarski(X12,X13) ) ),
    inference(resolution,[],[f133,f92])).

fof(f92,plain,(
    ! [X0] :
      ( r2_hidden(sK11(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK11(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK11(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f23,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK11(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK11(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f133,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f605,plain,
    ( ! [X9] :
        ( sK0 != sK11(X9)
        | ~ r2_hidden(sK1,X9)
        | k1_xboole_0 = X9 )
    | ~ spl14_3 ),
    inference(superposition,[],[f93,f148])).

fof(f148,plain,
    ( sK0 = k4_tarski(sK1,sK2)
    | ~ spl14_3 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl14_3
  <=> sK0 = k4_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f93,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK11(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f5717,plain,
    ( ! [X18] :
        ( sK0 != sK11(X18)
        | k1_xboole_0 = X18
        | ~ r2_hidden(sK0,X18) )
    | ~ spl14_169 ),
    inference(avatar_component_clause,[],[f5716])).

fof(f5716,plain,
    ( spl14_169
  <=> ! [X18] :
        ( sK0 != sK11(X18)
        | k1_xboole_0 = X18
        | ~ r2_hidden(sK0,X18) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_169])])).

fof(f5801,plain,
    ( spl14_169
    | ~ spl14_3
    | ~ spl14_18 ),
    inference(avatar_split_clause,[],[f5753,f353,f146,f5716])).

fof(f5753,plain,
    ( ! [X9] :
        ( ~ r2_hidden(sK0,X9)
        | sK0 != sK11(X9)
        | k1_xboole_0 = X9 )
    | ~ spl14_3
    | ~ spl14_18 ),
    inference(backward_demodulation,[],[f605,f355])).

fof(f5747,plain,
    ( spl14_18
    | ~ spl14_1
    | ~ spl14_3 ),
    inference(avatar_split_clause,[],[f5746,f146,f137,f353])).

fof(f137,plain,
    ( spl14_1
  <=> sK0 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f5746,plain,
    ( sK0 = sK1
    | ~ spl14_1
    | ~ spl14_3 ),
    inference(forward_demodulation,[],[f5727,f139])).

fof(f139,plain,
    ( sK0 = k1_mcart_1(sK0)
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f137])).

fof(f5727,plain,
    ( k1_mcart_1(sK0) = sK1
    | ~ spl14_3 ),
    inference(superposition,[],[f65,f148])).

fof(f65,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f5705,plain,
    ( ~ spl14_9
    | ~ spl14_168 ),
    inference(avatar_contradiction_clause,[],[f5704])).

fof(f5704,plain,
    ( $false
    | ~ spl14_9
    | ~ spl14_168 ),
    inference(subsumption_resolution,[],[f5666,f1305])).

fof(f1305,plain,
    ( ! [X13] : r1_tarski(k1_xboole_0,X13)
    | ~ spl14_9 ),
    inference(resolution,[],[f246,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK13(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK13(X0,X1),X1)
          & r2_hidden(sK13(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f56,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK13(X0,X1),X1)
        & r2_hidden(sK13(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f246,plain,
    ( ! [X4] : ~ r2_hidden(X4,k1_xboole_0)
    | ~ spl14_9 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl14_9
  <=> ! [X4] : ~ r2_hidden(X4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).

fof(f5666,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ spl14_168 ),
    inference(superposition,[],[f164,f5645])).

fof(f5645,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK0)
    | ~ spl14_168 ),
    inference(avatar_component_clause,[],[f5643])).

fof(f164,plain,(
    ! [X2,X3] : ~ r1_tarski(k2_tarski(X2,X3),X2) ),
    inference(resolution,[],[f101,f132])).

fof(f132,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f131])).

fof(f131,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f5646,plain,
    ( spl14_168
    | ~ spl14_3
    | ~ spl14_5 ),
    inference(avatar_split_clause,[],[f5641,f159,f146,f5643])).

fof(f159,plain,
    ( spl14_5
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f5641,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK0)
    | ~ spl14_3
    | ~ spl14_5 ),
    inference(equality_resolution,[],[f5634])).

fof(f5634,plain,
    ( ! [X36] :
        ( sK0 != X36
        | k1_xboole_0 = k2_tarski(X36,sK0) )
    | ~ spl14_3
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f5620,f130])).

fof(f5620,plain,
    ( ! [X36] :
        ( sK0 != X36
        | ~ r2_hidden(sK0,k2_tarski(X36,sK0))
        | k1_xboole_0 = k2_tarski(X36,sK0) )
    | ~ spl14_3
    | ~ spl14_5 ),
    inference(duplicate_literal_removal,[],[f5613])).

fof(f5613,plain,
    ( ! [X36] :
        ( sK0 != X36
        | ~ r2_hidden(sK0,k2_tarski(X36,sK0))
        | k1_xboole_0 = k2_tarski(X36,sK0)
        | k1_xboole_0 = k2_tarski(X36,sK0) )
    | ~ spl14_3
    | ~ spl14_5 ),
    inference(superposition,[],[f4223,f5591])).

fof(f5591,plain,
    ( ! [X0] :
        ( sK11(k2_tarski(X0,sK0)) = X0
        | k1_xboole_0 = k2_tarski(X0,sK0) )
    | ~ spl14_3
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f5590,f130])).

fof(f5590,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k2_tarski(X0,sK0))
        | k1_xboole_0 = k2_tarski(X0,sK0)
        | sK11(k2_tarski(X0,sK0)) = X0 )
    | ~ spl14_3
    | ~ spl14_5 ),
    inference(equality_resolution,[],[f4287])).

fof(f4287,plain,
    ( ! [X0,X1] :
        ( sK0 != X1
        | ~ r2_hidden(sK0,k2_tarski(X0,X1))
        | k2_tarski(X0,X1) = k1_xboole_0
        | sK11(k2_tarski(X0,X1)) = X0 )
    | ~ spl14_3
    | ~ spl14_5 ),
    inference(duplicate_literal_removal,[],[f4286])).

fof(f4286,plain,
    ( ! [X0,X1] :
        ( sK0 != X1
        | ~ r2_hidden(sK0,k2_tarski(X0,X1))
        | k2_tarski(X0,X1) = k1_xboole_0
        | sK11(k2_tarski(X0,X1)) = X0
        | k2_tarski(X0,X1) = k1_xboole_0 )
    | ~ spl14_3
    | ~ spl14_5 ),
    inference(superposition,[],[f4223,f310])).

fof(f4223,plain,
    ( ! [X10] :
        ( sK0 != sK11(X10)
        | ~ r2_hidden(sK0,X10)
        | k1_xboole_0 = X10 )
    | ~ spl14_3
    | ~ spl14_5 ),
    inference(backward_demodulation,[],[f606,f161])).

fof(f161,plain,
    ( sK0 = sK2
    | ~ spl14_5 ),
    inference(avatar_component_clause,[],[f159])).

fof(f606,plain,
    ( ! [X10] :
        ( sK0 != sK11(X10)
        | ~ r2_hidden(sK2,X10)
        | k1_xboole_0 = X10 )
    | ~ spl14_3 ),
    inference(superposition,[],[f94,f148])).

fof(f94,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK11(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f2899,plain,
    ( spl14_19
    | spl14_19
    | ~ spl14_8 ),
    inference(avatar_split_clause,[],[f2898,f241,f408,f408])).

fof(f408,plain,
    ( spl14_19
  <=> ! [X13,X12] : ~ r2_hidden(X12,X13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_19])])).

fof(f241,plain,
    ( spl14_8
  <=> ! [X3] : sK1 = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).

fof(f2898,plain,
    ( ! [X24,X23,X21,X22] :
        ( ~ r2_hidden(X23,X24)
        | ~ r2_hidden(X21,X22) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f2897,f127])).

fof(f127,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2897,plain,
    ( ! [X24,X23,X21,X22] :
        ( ~ r1_tarski(sK1,sK1)
        | ~ r2_hidden(X23,X24)
        | ~ r2_hidden(X21,X22) )
    | ~ spl14_8 ),
    inference(forward_demodulation,[],[f2723,f242])).

fof(f242,plain,
    ( ! [X3] : sK1 = X3
    | ~ spl14_8 ),
    inference(avatar_component_clause,[],[f241])).

fof(f2723,plain,
    ( ! [X24,X23,X21,X22] :
        ( ~ r1_tarski(sK1,k4_tarski(X23,X21))
        | ~ r2_hidden(X23,X24)
        | ~ r2_hidden(X21,X22) )
    | ~ spl14_8 ),
    inference(backward_demodulation,[],[f399,f242])).

fof(f399,plain,(
    ! [X24,X23,X21,X22] :
      ( ~ r1_tarski(k2_zfmisc_1(X24,X22),k4_tarski(X23,X21))
      | ~ r2_hidden(X23,X24)
      | ~ r2_hidden(X21,X22) ) ),
    inference(resolution,[],[f91,f101])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f983,plain,(
    ~ spl14_19 ),
    inference(avatar_contradiction_clause,[],[f966])).

fof(f966,plain,
    ( $false
    | ~ spl14_19 ),
    inference(unit_resulting_resolution,[],[f130,f409])).

fof(f409,plain,
    ( ! [X12,X13] : ~ r2_hidden(X12,X13)
    | ~ spl14_19 ),
    inference(avatar_component_clause,[],[f408])).

fof(f666,plain,
    ( spl14_9
    | spl14_8
    | ~ spl14_3 ),
    inference(avatar_split_clause,[],[f665,f146,f241,f245])).

fof(f665,plain,
    ( ! [X0,X1] :
        ( sK1 = X0
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl14_3 ),
    inference(subsumption_resolution,[],[f664,f197])).

fof(f197,plain,(
    ! [X0,X1] :
      ( k1_mcart_1(X1) = X0
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f63,f134])).

fof(f134,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f664,plain,
    ( ! [X0,X1] :
        ( k1_mcart_1(X1) != X0
        | sK1 = X0
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl14_3 ),
    inference(superposition,[],[f607,f197])).

fof(f607,plain,
    ( ! [X11] :
        ( sK3(sK0,X11) != X11
        | sK1 = X11 )
    | ~ spl14_3 ),
    inference(superposition,[],[f419,f148])).

fof(f419,plain,(
    ! [X6,X7,X1] :
      ( sK3(k4_tarski(X6,X7),X1) != X1
      | X1 = X6 ) ),
    inference(forward_demodulation,[],[f111,f65])).

fof(f111,plain,(
    ! [X6,X7,X1] :
      ( k1_mcart_1(k4_tarski(X6,X7)) = X1
      | sK3(k4_tarski(X6,X7),X1) != X1 ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X6,X0,X7,X1] :
      ( k1_mcart_1(X0) = X1
      | sK3(X0,X1) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ( sK3(X0,X1) != X1
              & k4_tarski(sK3(X0,X1),sK4(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X2
          & k4_tarski(X2,X3) = X0 )
     => ( sK3(X0,X1) != X1
        & k4_tarski(sK3(X0,X1),sK4(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ? [X2,X3] :
                ( X1 != X2
                & k4_tarski(X2,X3) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ( k1_mcart_1(X0) = X3
            | ? [X4,X5] :
                ( X3 != X4
                & k4_tarski(X4,X5) = X0 ) )
          & ( ! [X4,X5] :
                ( X3 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X3 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X4
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X4 ) ) ) ),
    inference(rectify,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k1_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_mcart_1)).

fof(f162,plain,
    ( spl14_5
    | ~ spl14_2
    | ~ spl14_3 ),
    inference(avatar_split_clause,[],[f157,f146,f141,f159])).

fof(f141,plain,
    ( spl14_2
  <=> sK0 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f157,plain,
    ( sK0 = sK2
    | ~ spl14_2
    | ~ spl14_3 ),
    inference(forward_demodulation,[],[f156,f143])).

fof(f143,plain,
    ( sK0 = k2_mcart_1(sK0)
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f141])).

fof(f156,plain,
    ( k2_mcart_1(sK0) = sK2
    | ~ spl14_3 ),
    inference(superposition,[],[f66,f148])).

fof(f66,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f14])).

fof(f149,plain,(
    spl14_3 ),
    inference(avatar_split_clause,[],[f61,f146])).

fof(f61,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK0
   => sK0 = k4_tarski(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f144,plain,
    ( spl14_1
    | spl14_2 ),
    inference(avatar_split_clause,[],[f62,f141,f137])).

fof(f62,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:19:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (23256)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.50  % (23261)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.19/0.51  % (23254)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.19/0.51  % (23280)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.19/0.52  % (23270)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.19/0.52  % (23272)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.19/0.52  % (23276)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.19/0.52  % (23274)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.19/0.52  % (23265)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.19/0.52  % (23282)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.19/0.53  % (23273)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.19/0.53  % (23271)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.19/0.53  % (23257)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.32/0.53  % (23275)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.32/0.53  % (23251)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.32/0.53  % (23261)Refutation not found, incomplete strategy% (23261)------------------------------
% 1.32/0.53  % (23261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (23252)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.32/0.53  % (23251)Refutation not found, incomplete strategy% (23251)------------------------------
% 1.32/0.53  % (23251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (23251)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (23251)Memory used [KB]: 1791
% 1.32/0.53  % (23251)Time elapsed: 0.114 s
% 1.32/0.53  % (23251)------------------------------
% 1.32/0.53  % (23251)------------------------------
% 1.32/0.53  % (23261)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (23261)Memory used [KB]: 10746
% 1.32/0.53  % (23261)Time elapsed: 0.123 s
% 1.32/0.53  % (23261)------------------------------
% 1.32/0.53  % (23261)------------------------------
% 1.32/0.53  % (23263)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.54  % (23266)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.32/0.54  % (23267)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.32/0.54  % (23253)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.54  % (23267)Refutation not found, incomplete strategy% (23267)------------------------------
% 1.32/0.54  % (23267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (23267)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (23267)Memory used [KB]: 6268
% 1.32/0.54  % (23267)Time elapsed: 0.002 s
% 1.32/0.54  % (23267)------------------------------
% 1.32/0.54  % (23267)------------------------------
% 1.32/0.54  % (23268)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.32/0.54  % (23258)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.32/0.54  % (23255)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.32/0.54  % (23260)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.32/0.55  % (23259)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.32/0.55  % (23279)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.55  % (23277)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.32/0.55  % (23278)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.32/0.55  % (23262)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.32/0.56  % (23269)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.32/0.56  % (23269)Refutation not found, incomplete strategy% (23269)------------------------------
% 1.32/0.56  % (23269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.57  % (23269)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.57  
% 1.32/0.57  % (23269)Memory used [KB]: 10618
% 1.32/0.57  % (23269)Time elapsed: 0.153 s
% 1.32/0.57  % (23269)------------------------------
% 1.32/0.57  % (23269)------------------------------
% 1.32/0.58  % (23262)Refutation not found, incomplete strategy% (23262)------------------------------
% 1.32/0.58  % (23262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.58  % (23262)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.58  
% 1.32/0.58  % (23262)Memory used [KB]: 10874
% 1.32/0.58  % (23262)Time elapsed: 0.170 s
% 1.32/0.58  % (23262)------------------------------
% 1.32/0.58  % (23262)------------------------------
% 1.99/0.64  % (23371)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.99/0.67  % (23377)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.99/0.68  % (23372)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.99/0.68  % (23388)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.43/0.72  % (23391)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.93/0.78  % (23391)Refutation not found, incomplete strategy% (23391)------------------------------
% 2.93/0.78  % (23391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.93/0.79  % (23391)Termination reason: Refutation not found, incomplete strategy
% 2.93/0.79  
% 2.93/0.79  % (23391)Memory used [KB]: 11257
% 2.93/0.79  % (23391)Time elapsed: 0.148 s
% 2.93/0.79  % (23391)------------------------------
% 2.93/0.79  % (23391)------------------------------
% 3.36/0.85  % (23256)Time limit reached!
% 3.36/0.85  % (23256)------------------------------
% 3.36/0.85  % (23256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.85  % (23256)Termination reason: Time limit
% 3.36/0.85  
% 3.36/0.85  % (23256)Memory used [KB]: 10874
% 3.36/0.85  % (23256)Time elapsed: 0.426 s
% 3.36/0.85  % (23256)------------------------------
% 3.36/0.85  % (23256)------------------------------
% 3.36/0.92  % (23263)Time limit reached!
% 3.36/0.92  % (23263)------------------------------
% 3.36/0.92  % (23263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.92  % (23263)Termination reason: Time limit
% 3.36/0.92  % (23252)Time limit reached!
% 3.36/0.92  % (23252)------------------------------
% 3.36/0.92  % (23252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.98/0.93  
% 3.98/0.93  % (23263)Memory used [KB]: 8571
% 3.98/0.93  % (23263)Time elapsed: 0.508 s
% 3.98/0.93  % (23263)------------------------------
% 3.98/0.93  % (23263)------------------------------
% 3.98/0.94  % (23252)Termination reason: Time limit
% 3.98/0.94  
% 3.98/0.94  % (23252)Memory used [KB]: 9210
% 3.98/0.94  % (23252)Time elapsed: 0.507 s
% 3.98/0.94  % (23252)------------------------------
% 3.98/0.94  % (23252)------------------------------
% 3.98/0.95  % (23459)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 3.98/0.97  % (23466)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.44/1.02  % (23280)Time limit reached!
% 4.44/1.02  % (23280)------------------------------
% 4.44/1.02  % (23280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.44/1.02  % (23280)Termination reason: Time limit
% 4.44/1.02  % (23280)Termination phase: Saturation
% 4.44/1.02  
% 4.44/1.02  % (23280)Memory used [KB]: 10362
% 4.44/1.02  % (23280)Time elapsed: 0.600 s
% 4.44/1.02  % (23280)------------------------------
% 4.44/1.02  % (23280)------------------------------
% 4.44/1.03  % (23388)Time limit reached!
% 4.44/1.03  % (23388)------------------------------
% 4.44/1.03  % (23388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.44/1.04  % (23268)Time limit reached!
% 4.44/1.04  % (23268)------------------------------
% 4.44/1.04  % (23268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.44/1.04  % (23268)Termination reason: Time limit
% 4.44/1.04  
% 4.44/1.04  % (23268)Memory used [KB]: 15479
% 4.44/1.04  % (23268)Time elapsed: 0.627 s
% 4.44/1.04  % (23268)------------------------------
% 4.44/1.04  % (23268)------------------------------
% 4.44/1.05  % (23388)Termination reason: Time limit
% 4.44/1.05  
% 4.44/1.05  % (23388)Memory used [KB]: 8443
% 4.44/1.05  % (23388)Time elapsed: 0.431 s
% 4.44/1.05  % (23388)------------------------------
% 4.44/1.05  % (23388)------------------------------
% 4.44/1.06  % (23467)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 4.44/1.06  % (23258)Time limit reached!
% 4.44/1.06  % (23258)------------------------------
% 4.44/1.06  % (23258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.44/1.06  % (23258)Termination reason: Time limit
% 4.44/1.06  % (23258)Termination phase: Saturation
% 4.44/1.06  
% 4.44/1.06  % (23258)Memory used [KB]: 10234
% 4.44/1.06  % (23258)Time elapsed: 0.600 s
% 4.44/1.06  % (23258)------------------------------
% 4.44/1.06  % (23258)------------------------------
% 4.98/1.07  % (23468)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.09/1.16  % (23471)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 6.09/1.16  % (23470)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.09/1.16  % (23469)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.09/1.20  % (23472)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 6.09/1.21  % (23273)Time limit reached!
% 6.09/1.21  % (23273)------------------------------
% 6.09/1.21  % (23273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.09/1.21  % (23273)Termination reason: Time limit
% 6.09/1.21  
% 6.09/1.21  % (23273)Memory used [KB]: 4093
% 6.09/1.21  % (23273)Time elapsed: 0.800 s
% 6.09/1.21  % (23273)------------------------------
% 6.09/1.21  % (23273)------------------------------
% 7.26/1.30  % (23473)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 7.26/1.31  % (23377)Refutation found. Thanks to Tanya!
% 7.26/1.31  % SZS status Theorem for theBenchmark
% 7.26/1.31  % SZS output start Proof for theBenchmark
% 7.26/1.31  fof(f7245,plain,(
% 7.26/1.31    $false),
% 7.26/1.31    inference(avatar_sat_refutation,[],[f144,f149,f162,f666,f983,f2899,f5646,f5705,f5747,f5801,f7244])).
% 7.26/1.31  fof(f7244,plain,(
% 7.26/1.31    ~spl14_3 | ~spl14_18 | spl14_168 | ~spl14_169),
% 7.26/1.31    inference(avatar_contradiction_clause,[],[f7243])).
% 7.26/1.31  fof(f7243,plain,(
% 7.26/1.31    $false | (~spl14_3 | ~spl14_18 | spl14_168 | ~spl14_169)),
% 7.26/1.31    inference(subsumption_resolution,[],[f7242,f5644])).
% 7.26/1.31  fof(f5644,plain,(
% 7.26/1.31    k1_xboole_0 != k2_tarski(sK0,sK0) | spl14_168),
% 7.26/1.31    inference(avatar_component_clause,[],[f5643])).
% 7.26/1.31  fof(f5643,plain,(
% 7.26/1.31    spl14_168 <=> k1_xboole_0 = k2_tarski(sK0,sK0)),
% 7.26/1.31    introduced(avatar_definition,[new_symbols(naming,[spl14_168])])).
% 7.26/1.31  fof(f7242,plain,(
% 7.26/1.31    k1_xboole_0 = k2_tarski(sK0,sK0) | (~spl14_3 | ~spl14_18 | ~spl14_169)),
% 7.26/1.31    inference(equality_resolution,[],[f7202])).
% 7.26/1.31  fof(f7202,plain,(
% 7.26/1.31    ( ! [X36] : (sK0 != X36 | k1_xboole_0 = k2_tarski(X36,sK0)) ) | (~spl14_3 | ~spl14_18 | ~spl14_169)),
% 7.26/1.31    inference(subsumption_resolution,[],[f7188,f130])).
% 7.26/1.31  fof(f130,plain,(
% 7.26/1.31    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 7.26/1.31    inference(equality_resolution,[],[f129])).
% 7.26/1.31  fof(f129,plain,(
% 7.26/1.31    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 7.26/1.31    inference(equality_resolution,[],[f97])).
% 7.26/1.31  fof(f97,plain,(
% 7.26/1.31    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.26/1.31    inference(cnf_transformation,[],[f54])).
% 7.26/1.31  fof(f54,plain,(
% 7.26/1.31    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK12(X0,X1,X2) != X1 & sK12(X0,X1,X2) != X0) | ~r2_hidden(sK12(X0,X1,X2),X2)) & (sK12(X0,X1,X2) = X1 | sK12(X0,X1,X2) = X0 | r2_hidden(sK12(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.26/1.31    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f52,f53])).
% 7.26/1.31  fof(f53,plain,(
% 7.26/1.31    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK12(X0,X1,X2) != X1 & sK12(X0,X1,X2) != X0) | ~r2_hidden(sK12(X0,X1,X2),X2)) & (sK12(X0,X1,X2) = X1 | sK12(X0,X1,X2) = X0 | r2_hidden(sK12(X0,X1,X2),X2))))),
% 7.26/1.31    introduced(choice_axiom,[])).
% 7.26/1.31  fof(f52,plain,(
% 7.26/1.31    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.26/1.31    inference(rectify,[],[f51])).
% 7.26/1.31  fof(f51,plain,(
% 7.26/1.31    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.26/1.31    inference(flattening,[],[f50])).
% 7.26/1.31  fof(f50,plain,(
% 7.26/1.31    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.26/1.31    inference(nnf_transformation,[],[f4])).
% 7.26/1.31  fof(f4,axiom,(
% 7.26/1.31    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.26/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 7.26/1.31  fof(f7188,plain,(
% 7.26/1.31    ( ! [X36] : (sK0 != X36 | k1_xboole_0 = k2_tarski(X36,sK0) | ~r2_hidden(sK0,k2_tarski(X36,sK0))) ) | (~spl14_3 | ~spl14_18 | ~spl14_169)),
% 7.26/1.31    inference(duplicate_literal_removal,[],[f7187])).
% 7.26/1.31  fof(f7187,plain,(
% 7.26/1.31    ( ! [X36] : (sK0 != X36 | k1_xboole_0 = k2_tarski(X36,sK0) | ~r2_hidden(sK0,k2_tarski(X36,sK0)) | k1_xboole_0 = k2_tarski(X36,sK0)) ) | (~spl14_3 | ~spl14_18 | ~spl14_169)),
% 7.26/1.31    inference(superposition,[],[f5717,f6799])).
% 7.26/1.31  fof(f6799,plain,(
% 7.26/1.31    ( ! [X0] : (sK11(k2_tarski(X0,sK0)) = X0 | k1_xboole_0 = k2_tarski(X0,sK0)) ) | (~spl14_3 | ~spl14_18)),
% 7.26/1.31    inference(subsumption_resolution,[],[f6798,f130])).
% 7.26/1.31  fof(f6798,plain,(
% 7.26/1.31    ( ! [X0] : (~r2_hidden(sK0,k2_tarski(X0,sK0)) | k1_xboole_0 = k2_tarski(X0,sK0) | sK11(k2_tarski(X0,sK0)) = X0) ) | (~spl14_3 | ~spl14_18)),
% 7.26/1.31    inference(equality_resolution,[],[f5761])).
% 7.26/1.31  fof(f5761,plain,(
% 7.26/1.31    ( ! [X0,X1] : (sK0 != X1 | ~r2_hidden(sK0,k2_tarski(X0,X1)) | k2_tarski(X0,X1) = k1_xboole_0 | sK11(k2_tarski(X0,X1)) = X0) ) | (~spl14_3 | ~spl14_18)),
% 7.26/1.31    inference(backward_demodulation,[],[f4285,f355])).
% 7.26/1.31  fof(f355,plain,(
% 7.26/1.31    sK0 = sK1 | ~spl14_18),
% 7.26/1.31    inference(avatar_component_clause,[],[f353])).
% 7.26/1.31  fof(f353,plain,(
% 7.26/1.31    spl14_18 <=> sK0 = sK1),
% 7.26/1.31    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).
% 7.26/1.31  fof(f4285,plain,(
% 7.26/1.31    ( ! [X0,X1] : (sK0 != X1 | ~r2_hidden(sK1,k2_tarski(X0,X1)) | k2_tarski(X0,X1) = k1_xboole_0 | sK11(k2_tarski(X0,X1)) = X0) ) | ~spl14_3),
% 7.26/1.31    inference(duplicate_literal_removal,[],[f4284])).
% 7.26/1.31  fof(f4284,plain,(
% 7.26/1.31    ( ! [X0,X1] : (sK0 != X1 | ~r2_hidden(sK1,k2_tarski(X0,X1)) | k2_tarski(X0,X1) = k1_xboole_0 | sK11(k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k1_xboole_0) ) | ~spl14_3),
% 7.26/1.31    inference(superposition,[],[f605,f310])).
% 7.26/1.31  fof(f310,plain,(
% 7.26/1.31    ( ! [X12,X13] : (sK11(k2_tarski(X12,X13)) = X13 | sK11(k2_tarski(X12,X13)) = X12 | k1_xboole_0 = k2_tarski(X12,X13)) )),
% 7.26/1.31    inference(resolution,[],[f133,f92])).
% 7.26/1.31  fof(f92,plain,(
% 7.26/1.31    ( ! [X0] : (r2_hidden(sK11(X0),X0) | k1_xboole_0 = X0) )),
% 7.26/1.31    inference(cnf_transformation,[],[f49])).
% 7.26/1.31  fof(f49,plain,(
% 7.26/1.31    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK11(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK11(X0),X0)) | k1_xboole_0 = X0)),
% 7.26/1.31    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f23,f48])).
% 7.26/1.31  fof(f48,plain,(
% 7.26/1.31    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK11(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK11(X0),X0)))),
% 7.26/1.31    introduced(choice_axiom,[])).
% 7.26/1.31  fof(f23,plain,(
% 7.26/1.31    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 7.26/1.31    inference(ennf_transformation,[],[f15])).
% 7.26/1.31  fof(f15,axiom,(
% 7.26/1.31    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 7.26/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 7.26/1.31  fof(f133,plain,(
% 7.26/1.31    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 7.26/1.31    inference(equality_resolution,[],[f95])).
% 7.26/1.31  fof(f95,plain,(
% 7.26/1.31    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 7.26/1.31    inference(cnf_transformation,[],[f54])).
% 7.26/1.31  fof(f605,plain,(
% 7.26/1.31    ( ! [X9] : (sK0 != sK11(X9) | ~r2_hidden(sK1,X9) | k1_xboole_0 = X9) ) | ~spl14_3),
% 7.26/1.31    inference(superposition,[],[f93,f148])).
% 7.26/1.31  fof(f148,plain,(
% 7.26/1.31    sK0 = k4_tarski(sK1,sK2) | ~spl14_3),
% 7.26/1.31    inference(avatar_component_clause,[],[f146])).
% 7.26/1.31  fof(f146,plain,(
% 7.26/1.31    spl14_3 <=> sK0 = k4_tarski(sK1,sK2)),
% 7.26/1.31    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).
% 7.26/1.31  fof(f93,plain,(
% 7.26/1.31    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK11(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 7.26/1.31    inference(cnf_transformation,[],[f49])).
% 7.26/1.31  fof(f5717,plain,(
% 7.26/1.31    ( ! [X18] : (sK0 != sK11(X18) | k1_xboole_0 = X18 | ~r2_hidden(sK0,X18)) ) | ~spl14_169),
% 7.26/1.31    inference(avatar_component_clause,[],[f5716])).
% 7.26/1.31  fof(f5716,plain,(
% 7.26/1.31    spl14_169 <=> ! [X18] : (sK0 != sK11(X18) | k1_xboole_0 = X18 | ~r2_hidden(sK0,X18))),
% 7.26/1.31    introduced(avatar_definition,[new_symbols(naming,[spl14_169])])).
% 7.26/1.31  fof(f5801,plain,(
% 7.26/1.31    spl14_169 | ~spl14_3 | ~spl14_18),
% 7.26/1.31    inference(avatar_split_clause,[],[f5753,f353,f146,f5716])).
% 7.26/1.31  fof(f5753,plain,(
% 7.26/1.31    ( ! [X9] : (~r2_hidden(sK0,X9) | sK0 != sK11(X9) | k1_xboole_0 = X9) ) | (~spl14_3 | ~spl14_18)),
% 7.26/1.31    inference(backward_demodulation,[],[f605,f355])).
% 7.26/1.31  fof(f5747,plain,(
% 7.26/1.31    spl14_18 | ~spl14_1 | ~spl14_3),
% 7.26/1.31    inference(avatar_split_clause,[],[f5746,f146,f137,f353])).
% 7.26/1.31  fof(f137,plain,(
% 7.26/1.31    spl14_1 <=> sK0 = k1_mcart_1(sK0)),
% 7.26/1.31    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).
% 7.26/1.31  fof(f5746,plain,(
% 7.26/1.31    sK0 = sK1 | (~spl14_1 | ~spl14_3)),
% 7.26/1.31    inference(forward_demodulation,[],[f5727,f139])).
% 7.26/1.31  fof(f139,plain,(
% 7.26/1.31    sK0 = k1_mcart_1(sK0) | ~spl14_1),
% 7.26/1.31    inference(avatar_component_clause,[],[f137])).
% 7.26/1.31  fof(f5727,plain,(
% 7.26/1.31    k1_mcart_1(sK0) = sK1 | ~spl14_3),
% 7.26/1.31    inference(superposition,[],[f65,f148])).
% 7.26/1.31  fof(f65,plain,(
% 7.26/1.31    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 7.26/1.31    inference(cnf_transformation,[],[f14])).
% 7.26/1.31  fof(f14,axiom,(
% 7.26/1.31    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 7.26/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 7.26/1.31  fof(f5705,plain,(
% 7.26/1.31    ~spl14_9 | ~spl14_168),
% 7.26/1.31    inference(avatar_contradiction_clause,[],[f5704])).
% 7.26/1.31  fof(f5704,plain,(
% 7.26/1.31    $false | (~spl14_9 | ~spl14_168)),
% 7.26/1.31    inference(subsumption_resolution,[],[f5666,f1305])).
% 7.26/1.31  fof(f1305,plain,(
% 7.26/1.31    ( ! [X13] : (r1_tarski(k1_xboole_0,X13)) ) | ~spl14_9),
% 7.26/1.31    inference(resolution,[],[f246,f103])).
% 7.26/1.31  fof(f103,plain,(
% 7.26/1.31    ( ! [X0,X1] : (r2_hidden(sK13(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 7.26/1.31    inference(cnf_transformation,[],[f58])).
% 7.26/1.31  fof(f58,plain,(
% 7.26/1.31    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK13(X0,X1),X1) & r2_hidden(sK13(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.26/1.31    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f56,f57])).
% 7.26/1.31  fof(f57,plain,(
% 7.26/1.31    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK13(X0,X1),X1) & r2_hidden(sK13(X0,X1),X0)))),
% 7.26/1.31    introduced(choice_axiom,[])).
% 7.26/1.31  fof(f56,plain,(
% 7.26/1.31    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.26/1.31    inference(rectify,[],[f55])).
% 7.26/1.31  fof(f55,plain,(
% 7.26/1.31    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.26/1.31    inference(nnf_transformation,[],[f25])).
% 7.26/1.31  fof(f25,plain,(
% 7.26/1.31    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.26/1.31    inference(ennf_transformation,[],[f1])).
% 7.26/1.31  fof(f1,axiom,(
% 7.26/1.31    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.26/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 7.26/1.31  fof(f246,plain,(
% 7.26/1.31    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0)) ) | ~spl14_9),
% 7.26/1.31    inference(avatar_component_clause,[],[f245])).
% 7.26/1.31  fof(f245,plain,(
% 7.26/1.31    spl14_9 <=> ! [X4] : ~r2_hidden(X4,k1_xboole_0)),
% 7.26/1.31    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).
% 7.26/1.31  fof(f5666,plain,(
% 7.26/1.31    ~r1_tarski(k1_xboole_0,sK0) | ~spl14_168),
% 7.26/1.31    inference(superposition,[],[f164,f5645])).
% 7.26/1.31  fof(f5645,plain,(
% 7.26/1.31    k1_xboole_0 = k2_tarski(sK0,sK0) | ~spl14_168),
% 7.26/1.31    inference(avatar_component_clause,[],[f5643])).
% 7.26/1.31  fof(f164,plain,(
% 7.26/1.31    ( ! [X2,X3] : (~r1_tarski(k2_tarski(X2,X3),X2)) )),
% 7.26/1.31    inference(resolution,[],[f101,f132])).
% 7.26/1.31  fof(f132,plain,(
% 7.26/1.31    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 7.26/1.31    inference(equality_resolution,[],[f131])).
% 7.26/1.31  fof(f131,plain,(
% 7.26/1.31    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 7.26/1.31    inference(equality_resolution,[],[f96])).
% 7.26/1.31  fof(f96,plain,(
% 7.26/1.31    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.26/1.31    inference(cnf_transformation,[],[f54])).
% 7.26/1.31  fof(f101,plain,(
% 7.26/1.31    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 7.26/1.31    inference(cnf_transformation,[],[f24])).
% 7.26/1.31  fof(f24,plain,(
% 7.26/1.31    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.26/1.31    inference(ennf_transformation,[],[f11])).
% 7.26/1.31  fof(f11,axiom,(
% 7.26/1.31    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.26/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 7.26/1.31  fof(f5646,plain,(
% 7.26/1.31    spl14_168 | ~spl14_3 | ~spl14_5),
% 7.26/1.31    inference(avatar_split_clause,[],[f5641,f159,f146,f5643])).
% 7.26/1.31  fof(f159,plain,(
% 7.26/1.31    spl14_5 <=> sK0 = sK2),
% 7.26/1.31    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).
% 7.26/1.31  fof(f5641,plain,(
% 7.26/1.31    k1_xboole_0 = k2_tarski(sK0,sK0) | (~spl14_3 | ~spl14_5)),
% 7.26/1.31    inference(equality_resolution,[],[f5634])).
% 7.26/1.31  fof(f5634,plain,(
% 7.26/1.31    ( ! [X36] : (sK0 != X36 | k1_xboole_0 = k2_tarski(X36,sK0)) ) | (~spl14_3 | ~spl14_5)),
% 7.26/1.31    inference(subsumption_resolution,[],[f5620,f130])).
% 7.26/1.31  fof(f5620,plain,(
% 7.26/1.31    ( ! [X36] : (sK0 != X36 | ~r2_hidden(sK0,k2_tarski(X36,sK0)) | k1_xboole_0 = k2_tarski(X36,sK0)) ) | (~spl14_3 | ~spl14_5)),
% 7.26/1.31    inference(duplicate_literal_removal,[],[f5613])).
% 7.26/1.31  fof(f5613,plain,(
% 7.26/1.31    ( ! [X36] : (sK0 != X36 | ~r2_hidden(sK0,k2_tarski(X36,sK0)) | k1_xboole_0 = k2_tarski(X36,sK0) | k1_xboole_0 = k2_tarski(X36,sK0)) ) | (~spl14_3 | ~spl14_5)),
% 7.26/1.31    inference(superposition,[],[f4223,f5591])).
% 7.26/1.31  fof(f5591,plain,(
% 7.26/1.31    ( ! [X0] : (sK11(k2_tarski(X0,sK0)) = X0 | k1_xboole_0 = k2_tarski(X0,sK0)) ) | (~spl14_3 | ~spl14_5)),
% 7.26/1.31    inference(subsumption_resolution,[],[f5590,f130])).
% 7.26/1.31  fof(f5590,plain,(
% 7.26/1.31    ( ! [X0] : (~r2_hidden(sK0,k2_tarski(X0,sK0)) | k1_xboole_0 = k2_tarski(X0,sK0) | sK11(k2_tarski(X0,sK0)) = X0) ) | (~spl14_3 | ~spl14_5)),
% 7.26/1.31    inference(equality_resolution,[],[f4287])).
% 7.26/1.31  fof(f4287,plain,(
% 7.26/1.31    ( ! [X0,X1] : (sK0 != X1 | ~r2_hidden(sK0,k2_tarski(X0,X1)) | k2_tarski(X0,X1) = k1_xboole_0 | sK11(k2_tarski(X0,X1)) = X0) ) | (~spl14_3 | ~spl14_5)),
% 7.26/1.31    inference(duplicate_literal_removal,[],[f4286])).
% 7.26/1.31  fof(f4286,plain,(
% 7.26/1.31    ( ! [X0,X1] : (sK0 != X1 | ~r2_hidden(sK0,k2_tarski(X0,X1)) | k2_tarski(X0,X1) = k1_xboole_0 | sK11(k2_tarski(X0,X1)) = X0 | k2_tarski(X0,X1) = k1_xboole_0) ) | (~spl14_3 | ~spl14_5)),
% 7.26/1.31    inference(superposition,[],[f4223,f310])).
% 7.26/1.31  fof(f4223,plain,(
% 7.26/1.31    ( ! [X10] : (sK0 != sK11(X10) | ~r2_hidden(sK0,X10) | k1_xboole_0 = X10) ) | (~spl14_3 | ~spl14_5)),
% 7.26/1.31    inference(backward_demodulation,[],[f606,f161])).
% 7.26/1.31  fof(f161,plain,(
% 7.26/1.31    sK0 = sK2 | ~spl14_5),
% 7.26/1.31    inference(avatar_component_clause,[],[f159])).
% 7.26/1.31  fof(f606,plain,(
% 7.26/1.31    ( ! [X10] : (sK0 != sK11(X10) | ~r2_hidden(sK2,X10) | k1_xboole_0 = X10) ) | ~spl14_3),
% 7.26/1.31    inference(superposition,[],[f94,f148])).
% 7.26/1.31  fof(f94,plain,(
% 7.26/1.31    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK11(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 7.26/1.31    inference(cnf_transformation,[],[f49])).
% 7.26/1.31  fof(f2899,plain,(
% 7.26/1.31    spl14_19 | spl14_19 | ~spl14_8),
% 7.26/1.31    inference(avatar_split_clause,[],[f2898,f241,f408,f408])).
% 7.26/1.31  fof(f408,plain,(
% 7.26/1.31    spl14_19 <=> ! [X13,X12] : ~r2_hidden(X12,X13)),
% 7.26/1.31    introduced(avatar_definition,[new_symbols(naming,[spl14_19])])).
% 7.26/1.31  fof(f241,plain,(
% 7.26/1.31    spl14_8 <=> ! [X3] : sK1 = X3),
% 7.26/1.31    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).
% 7.26/1.31  fof(f2898,plain,(
% 7.26/1.31    ( ! [X24,X23,X21,X22] : (~r2_hidden(X23,X24) | ~r2_hidden(X21,X22)) ) | ~spl14_8),
% 7.26/1.31    inference(subsumption_resolution,[],[f2897,f127])).
% 7.26/1.31  fof(f127,plain,(
% 7.26/1.31    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.26/1.31    inference(equality_resolution,[],[f87])).
% 7.26/1.31  fof(f87,plain,(
% 7.26/1.31    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.26/1.31    inference(cnf_transformation,[],[f45])).
% 7.26/1.31  fof(f45,plain,(
% 7.26/1.31    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.26/1.31    inference(flattening,[],[f44])).
% 7.26/1.31  fof(f44,plain,(
% 7.26/1.31    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.26/1.31    inference(nnf_transformation,[],[f2])).
% 7.26/1.31  fof(f2,axiom,(
% 7.26/1.31    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.26/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 7.26/1.31  fof(f2897,plain,(
% 7.26/1.31    ( ! [X24,X23,X21,X22] : (~r1_tarski(sK1,sK1) | ~r2_hidden(X23,X24) | ~r2_hidden(X21,X22)) ) | ~spl14_8),
% 7.26/1.31    inference(forward_demodulation,[],[f2723,f242])).
% 7.26/1.31  fof(f242,plain,(
% 7.26/1.31    ( ! [X3] : (sK1 = X3) ) | ~spl14_8),
% 7.26/1.31    inference(avatar_component_clause,[],[f241])).
% 7.26/1.31  fof(f2723,plain,(
% 7.26/1.31    ( ! [X24,X23,X21,X22] : (~r1_tarski(sK1,k4_tarski(X23,X21)) | ~r2_hidden(X23,X24) | ~r2_hidden(X21,X22)) ) | ~spl14_8),
% 7.26/1.31    inference(backward_demodulation,[],[f399,f242])).
% 7.26/1.31  fof(f399,plain,(
% 7.26/1.31    ( ! [X24,X23,X21,X22] : (~r1_tarski(k2_zfmisc_1(X24,X22),k4_tarski(X23,X21)) | ~r2_hidden(X23,X24) | ~r2_hidden(X21,X22)) )),
% 7.26/1.31    inference(resolution,[],[f91,f101])).
% 7.26/1.31  fof(f91,plain,(
% 7.26/1.31    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 7.26/1.31    inference(cnf_transformation,[],[f47])).
% 7.26/1.31  fof(f47,plain,(
% 7.26/1.31    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.26/1.31    inference(flattening,[],[f46])).
% 7.26/1.31  fof(f46,plain,(
% 7.26/1.31    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.26/1.31    inference(nnf_transformation,[],[f9])).
% 7.26/1.31  fof(f9,axiom,(
% 7.26/1.31    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 7.26/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 7.26/1.31  fof(f983,plain,(
% 7.26/1.31    ~spl14_19),
% 7.26/1.31    inference(avatar_contradiction_clause,[],[f966])).
% 7.26/1.31  fof(f966,plain,(
% 7.26/1.31    $false | ~spl14_19),
% 7.26/1.31    inference(unit_resulting_resolution,[],[f130,f409])).
% 7.26/1.31  fof(f409,plain,(
% 7.26/1.31    ( ! [X12,X13] : (~r2_hidden(X12,X13)) ) | ~spl14_19),
% 7.26/1.31    inference(avatar_component_clause,[],[f408])).
% 7.26/1.31  fof(f666,plain,(
% 7.26/1.31    spl14_9 | spl14_8 | ~spl14_3),
% 7.26/1.31    inference(avatar_split_clause,[],[f665,f146,f241,f245])).
% 7.26/1.31  fof(f665,plain,(
% 7.26/1.31    ( ! [X0,X1] : (sK1 = X0 | ~r2_hidden(X1,k1_xboole_0)) ) | ~spl14_3),
% 7.26/1.31    inference(subsumption_resolution,[],[f664,f197])).
% 7.26/1.31  fof(f197,plain,(
% 7.26/1.31    ( ! [X0,X1] : (k1_mcart_1(X1) = X0 | ~r2_hidden(X1,k1_xboole_0)) )),
% 7.26/1.31    inference(superposition,[],[f63,f134])).
% 7.26/1.31  fof(f134,plain,(
% 7.26/1.31    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.26/1.31    inference(equality_resolution,[],[f107])).
% 7.26/1.31  fof(f107,plain,(
% 7.26/1.31    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 7.26/1.31    inference(cnf_transformation,[],[f60])).
% 7.26/1.31  fof(f60,plain,(
% 7.26/1.31    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 7.26/1.31    inference(flattening,[],[f59])).
% 7.26/1.31  fof(f59,plain,(
% 7.26/1.31    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 7.26/1.31    inference(nnf_transformation,[],[f10])).
% 7.26/1.31  fof(f10,axiom,(
% 7.26/1.31    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.26/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 7.26/1.31  fof(f63,plain,(
% 7.26/1.31    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) | k1_mcart_1(X0) = X1) )),
% 7.26/1.31    inference(cnf_transformation,[],[f20])).
% 7.26/1.31  fof(f20,plain,(
% 7.26/1.31    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 7.26/1.31    inference(ennf_transformation,[],[f13])).
% 7.26/1.31  fof(f13,axiom,(
% 7.26/1.31    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 7.26/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).
% 7.26/1.31  fof(f664,plain,(
% 7.26/1.31    ( ! [X0,X1] : (k1_mcart_1(X1) != X0 | sK1 = X0 | ~r2_hidden(X1,k1_xboole_0)) ) | ~spl14_3),
% 7.26/1.31    inference(superposition,[],[f607,f197])).
% 7.26/1.31  fof(f607,plain,(
% 7.26/1.31    ( ! [X11] : (sK3(sK0,X11) != X11 | sK1 = X11) ) | ~spl14_3),
% 7.26/1.31    inference(superposition,[],[f419,f148])).
% 7.26/1.31  fof(f419,plain,(
% 7.26/1.31    ( ! [X6,X7,X1] : (sK3(k4_tarski(X6,X7),X1) != X1 | X1 = X6) )),
% 7.26/1.31    inference(forward_demodulation,[],[f111,f65])).
% 7.26/1.31  fof(f111,plain,(
% 7.26/1.31    ( ! [X6,X7,X1] : (k1_mcart_1(k4_tarski(X6,X7)) = X1 | sK3(k4_tarski(X6,X7),X1) != X1) )),
% 7.26/1.31    inference(equality_resolution,[],[f69])).
% 7.26/1.31  fof(f69,plain,(
% 7.26/1.31    ( ! [X6,X0,X7,X1] : (k1_mcart_1(X0) = X1 | sK3(X0,X1) != X1 | k4_tarski(X6,X7) != X0) )),
% 7.26/1.31    inference(cnf_transformation,[],[f32])).
% 7.26/1.31  fof(f32,plain,(
% 7.26/1.31    ! [X0] : (! [X1] : ((k1_mcart_1(X0) = X1 | (sK3(X0,X1) != X1 & k4_tarski(sK3(X0,X1),sK4(X0,X1)) = X0)) & (! [X4,X5] : (X1 = X4 | k4_tarski(X4,X5) != X0) | k1_mcart_1(X0) != X1)) | ! [X6,X7] : k4_tarski(X6,X7) != X0)),
% 7.26/1.31    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f30,f31])).
% 7.26/1.31  fof(f31,plain,(
% 7.26/1.31    ! [X1,X0] : (? [X2,X3] : (X1 != X2 & k4_tarski(X2,X3) = X0) => (sK3(X0,X1) != X1 & k4_tarski(sK3(X0,X1),sK4(X0,X1)) = X0))),
% 7.26/1.31    introduced(choice_axiom,[])).
% 7.26/1.31  fof(f30,plain,(
% 7.26/1.31    ! [X0] : (! [X1] : ((k1_mcart_1(X0) = X1 | ? [X2,X3] : (X1 != X2 & k4_tarski(X2,X3) = X0)) & (! [X4,X5] : (X1 = X4 | k4_tarski(X4,X5) != X0) | k1_mcart_1(X0) != X1)) | ! [X6,X7] : k4_tarski(X6,X7) != X0)),
% 7.26/1.31    inference(rectify,[],[f29])).
% 7.26/1.31  fof(f29,plain,(
% 7.26/1.31    ! [X0] : (! [X3] : ((k1_mcart_1(X0) = X3 | ? [X4,X5] : (X3 != X4 & k4_tarski(X4,X5) = X0)) & (! [X4,X5] : (X3 = X4 | k4_tarski(X4,X5) != X0) | k1_mcart_1(X0) != X3)) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 7.26/1.31    inference(nnf_transformation,[],[f21])).
% 7.26/1.31  fof(f21,plain,(
% 7.26/1.31    ! [X0] : (! [X3] : (k1_mcart_1(X0) = X3 <=> ! [X4,X5] : (X3 = X4 | k4_tarski(X4,X5) != X0)) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 7.26/1.31    inference(ennf_transformation,[],[f18])).
% 7.26/1.31  fof(f18,plain,(
% 7.26/1.31    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => ! [X3] : (k1_mcart_1(X0) = X3 <=> ! [X4,X5] : (k4_tarski(X4,X5) = X0 => X3 = X4)))),
% 7.26/1.31    inference(rectify,[],[f12])).
% 7.26/1.31  fof(f12,axiom,(
% 7.26/1.31    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => ! [X1] : (k1_mcart_1(X0) = X1 <=> ! [X2,X3] : (k4_tarski(X2,X3) = X0 => X1 = X2)))),
% 7.26/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_mcart_1)).
% 7.26/1.31  fof(f162,plain,(
% 7.26/1.31    spl14_5 | ~spl14_2 | ~spl14_3),
% 7.26/1.31    inference(avatar_split_clause,[],[f157,f146,f141,f159])).
% 7.26/1.31  fof(f141,plain,(
% 7.26/1.31    spl14_2 <=> sK0 = k2_mcart_1(sK0)),
% 7.26/1.31    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).
% 7.26/1.31  fof(f157,plain,(
% 7.26/1.31    sK0 = sK2 | (~spl14_2 | ~spl14_3)),
% 7.26/1.31    inference(forward_demodulation,[],[f156,f143])).
% 7.26/1.31  fof(f143,plain,(
% 7.26/1.31    sK0 = k2_mcart_1(sK0) | ~spl14_2),
% 7.26/1.31    inference(avatar_component_clause,[],[f141])).
% 7.26/1.31  fof(f156,plain,(
% 7.26/1.31    k2_mcart_1(sK0) = sK2 | ~spl14_3),
% 7.26/1.31    inference(superposition,[],[f66,f148])).
% 7.26/1.31  fof(f66,plain,(
% 7.26/1.31    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 7.26/1.31    inference(cnf_transformation,[],[f14])).
% 7.26/1.31  fof(f149,plain,(
% 7.26/1.31    spl14_3),
% 7.26/1.31    inference(avatar_split_clause,[],[f61,f146])).
% 7.26/1.31  fof(f61,plain,(
% 7.26/1.31    sK0 = k4_tarski(sK1,sK2)),
% 7.26/1.31    inference(cnf_transformation,[],[f28])).
% 7.26/1.31  fof(f28,plain,(
% 7.26/1.31    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & sK0 = k4_tarski(sK1,sK2)),
% 7.26/1.31    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f27,f26])).
% 7.26/1.31  fof(f26,plain,(
% 7.26/1.31    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & ? [X2,X1] : k4_tarski(X1,X2) = sK0)),
% 7.26/1.31    introduced(choice_axiom,[])).
% 7.26/1.31  fof(f27,plain,(
% 7.26/1.31    ? [X2,X1] : k4_tarski(X1,X2) = sK0 => sK0 = k4_tarski(sK1,sK2)),
% 7.26/1.31    introduced(choice_axiom,[])).
% 7.26/1.31  fof(f19,plain,(
% 7.26/1.31    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 7.26/1.31    inference(ennf_transformation,[],[f17])).
% 7.26/1.31  fof(f17,negated_conjecture,(
% 7.26/1.31    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 7.26/1.31    inference(negated_conjecture,[],[f16])).
% 7.26/1.31  fof(f16,conjecture,(
% 7.26/1.31    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 7.26/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 7.26/1.31  fof(f144,plain,(
% 7.26/1.31    spl14_1 | spl14_2),
% 7.26/1.31    inference(avatar_split_clause,[],[f62,f141,f137])).
% 7.26/1.31  fof(f62,plain,(
% 7.26/1.31    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 7.26/1.31    inference(cnf_transformation,[],[f28])).
% 7.26/1.31  % SZS output end Proof for theBenchmark
% 7.26/1.31  % (23377)------------------------------
% 7.26/1.31  % (23377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.26/1.31  % (23377)Termination reason: Refutation
% 7.26/1.31  
% 7.26/1.31  % (23377)Memory used [KB]: 10362
% 7.26/1.31  % (23377)Time elapsed: 0.738 s
% 7.26/1.31  % (23377)------------------------------
% 7.26/1.31  % (23377)------------------------------
% 7.26/1.31  % (23248)Success in time 0.944 s
%------------------------------------------------------------------------------
