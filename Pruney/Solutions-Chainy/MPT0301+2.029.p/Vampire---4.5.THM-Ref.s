%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 191 expanded)
%              Number of leaves         :   22 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  302 ( 662 expanded)
%              Number of equality atoms :   83 ( 223 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f408,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f73,f74,f92,f104,f110,f133,f137,f357,f372,f394])).

fof(f394,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_12 ),
    inference(avatar_contradiction_clause,[],[f393])).

fof(f393,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f386,f300])).

fof(f300,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f261,f41])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f261,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f224,f59,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X4,X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(sK6(X0,X1,X2),X1,X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sP0(sK6(X0,X1,X2),X1,X0)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X3,X1,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X3,X1,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(sK6(X0,X1,X2),X1,X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sP0(sK6(X0,X1,X2),X1,X0)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X3,X1,X0) )
            & ( sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X3,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f59,plain,(
    ! [X0,X1] : sP1(X0,X1,k2_zfmisc_1(X0,X1)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f6,f15,f14])).

fof(f14,plain,(
    ! [X3,X1,X0] :
      ( sP0(X3,X1,X0)
    <=> ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X4,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f224,plain,
    ( ! [X0,X1] : ~ sP0(X0,k1_xboole_0,X1)
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f132,f50])).

% (23624)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3,X4] :
            ( k4_tarski(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ( k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) = X0
          & r2_hidden(sK8(X0,X1,X2),X1)
          & r2_hidden(sK7(X0,X1,X2),X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X5,X6] :
          ( k4_tarski(X5,X6) = X0
          & r2_hidden(X6,X1)
          & r2_hidden(X5,X2) )
     => ( k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) = X0
        & r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(sK7(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3,X4] :
            ( k4_tarski(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ? [X5,X6] :
            ( k4_tarski(X5,X6) = X0
            & r2_hidden(X6,X1)
            & r2_hidden(X5,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X3,X1,X0] :
      ( ( sP0(X3,X1,X0)
        | ! [X4,X5] :
            ( k4_tarski(X4,X5) != X3
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X0) ) )
      & ( ? [X4,X5] :
            ( k4_tarski(X4,X5) = X3
            & r2_hidden(X5,X1)
            & r2_hidden(X4,X0) )
        | ~ sP0(X3,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f132,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl9_12
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f386,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,k1_xboole_0)
    | spl9_1
    | ~ spl9_2 ),
    inference(backward_demodulation,[],[f63,f66])).

fof(f66,plain,
    ( k1_xboole_0 = sK3
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl9_2
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f63,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,sK3)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl9_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f372,plain,
    ( spl9_1
    | ~ spl9_3
    | ~ spl9_12 ),
    inference(avatar_contradiction_clause,[],[f371])).

fof(f371,plain,
    ( $false
    | spl9_1
    | ~ spl9_3
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f370,f279])).

fof(f279,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f260,f41])).

fof(f260,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f210,f59,f45])).

fof(f210,plain,
    ( ! [X0,X1] : ~ sP0(X0,X1,k1_xboole_0)
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f132,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f370,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | spl9_1
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f63,f71])).

fof(f71,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl9_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f357,plain,
    ( ~ spl9_6
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_12 ),
    inference(avatar_contradiction_clause,[],[f356])).

fof(f356,plain,
    ( $false
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f341,f266])).

fof(f266,plain,
    ( ! [X0] : ~ sP0(X0,sK3,sK2)
    | ~ spl9_9
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f132,f109,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X4,X1,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f109,plain,
    ( sP1(sK2,sK3,k1_xboole_0)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl9_9
  <=> sP1(sK2,sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f341,plain,
    ( sP0(k4_tarski(sK4(sK2),sK4(sK3)),sK3,sK2)
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(unit_resulting_resolution,[],[f91,f103,f58])).

fof(f58,plain,(
    ! [X4,X2,X3,X1] :
      ( sP0(k4_tarski(X3,X4),X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X3,X2) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | k4_tarski(X3,X4) != X0
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X3,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f103,plain,
    ( r2_hidden(sK4(sK3),sK3)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl9_8
  <=> r2_hidden(sK4(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f91,plain,
    ( r2_hidden(sK4(sK2),sK2)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl9_6
  <=> r2_hidden(sK4(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f137,plain,(
    ~ spl9_11 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f121,f129])).

fof(f129,plain,
    ( ! [X0] : ~ r1_xboole_0(X0,k1_xboole_0)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl9_11
  <=> ! [X0] : ~ r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f121,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f119,f40])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f119,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f42,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f42,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f133,plain,
    ( spl9_11
    | spl9_12 ),
    inference(avatar_split_clause,[],[f126,f131,f128])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f44,f39])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f110,plain,
    ( spl9_9
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f105,f61,f107])).

fof(f105,plain,
    ( sP1(sK2,sK3,k1_xboole_0)
    | ~ spl9_1 ),
    inference(superposition,[],[f59,f62])).

fof(f62,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK2,sK3)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f104,plain,
    ( spl9_8
    | spl9_2 ),
    inference(avatar_split_clause,[],[f99,f65,f101])).

fof(f99,plain,
    ( r2_hidden(sK4(sK3),sK3)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f67,f41])).

fof(f67,plain,
    ( k1_xboole_0 != sK3
    | spl9_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f92,plain,
    ( spl9_6
    | spl9_3 ),
    inference(avatar_split_clause,[],[f81,f70,f89])).

fof(f81,plain,
    ( r2_hidden(sK4(sK2),sK2)
    | spl9_3 ),
    inference(unit_resulting_resolution,[],[f72,f41])).

fof(f72,plain,
    ( k1_xboole_0 != sK2
    | spl9_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f74,plain,
    ( spl9_1
    | spl9_3
    | spl9_2 ),
    inference(avatar_split_clause,[],[f36,f65,f70,f61])).

fof(f36,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ( k1_xboole_0 != sK3
        & k1_xboole_0 != sK2 )
      | k1_xboole_0 != k2_zfmisc_1(sK2,sK3) )
    & ( k1_xboole_0 = sK3
      | k1_xboole_0 = sK2
      | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK3
          & k1_xboole_0 != sK2 )
        | k1_xboole_0 != k2_zfmisc_1(sK2,sK3) )
      & ( k1_xboole_0 = sK3
        | k1_xboole_0 = sK2
        | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f73,plain,
    ( ~ spl9_1
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f37,f70,f61])).

fof(f37,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f38,f65,f61])).

fof(f38,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:59:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.45  % (23642)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.45  % (23642)Refutation not found, incomplete strategy% (23642)------------------------------
% 0.22/0.45  % (23642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (23642)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.45  
% 0.22/0.45  % (23642)Memory used [KB]: 10618
% 0.22/0.45  % (23642)Time elapsed: 0.005 s
% 0.22/0.45  % (23642)------------------------------
% 0.22/0.45  % (23642)------------------------------
% 0.22/0.47  % (23634)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (23641)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.49  % (23631)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (23627)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (23629)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (23638)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (23635)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (23632)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (23632)Refutation not found, incomplete strategy% (23632)------------------------------
% 0.22/0.50  % (23632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (23632)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (23632)Memory used [KB]: 6012
% 0.22/0.50  % (23632)Time elapsed: 0.083 s
% 0.22/0.50  % (23632)------------------------------
% 0.22/0.50  % (23632)------------------------------
% 0.22/0.50  % (23636)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (23628)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (23638)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f408,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f68,f73,f74,f92,f104,f110,f133,f137,f357,f372,f394])).
% 0.22/0.50  fof(f394,plain,(
% 0.22/0.50    spl9_1 | ~spl9_2 | ~spl9_12),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f393])).
% 0.22/0.50  fof(f393,plain,(
% 0.22/0.50    $false | (spl9_1 | ~spl9_2 | ~spl9_12)),
% 0.22/0.50    inference(subsumption_resolution,[],[f386,f300])).
% 0.22/0.50  fof(f300,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl9_12),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f261,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.50  fof(f261,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))) ) | ~spl9_12),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f224,f59,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X4,X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(sK6(X0,X1,X2),X1,X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP0(sK6(X0,X1,X2),X1,X0) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2))) => ((~sP0(sK6(X0,X1,X2),X1,X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP0(sK6(X0,X1,X2),X1,X0) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.22/0.50    inference(rectify,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X3,X1,X0)) & (sP0(X3,X1,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 0.22/0.50    inference(nnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X3,X1,X0)))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X0,X1] : (sP1(X0,X1,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.50    inference(equality_resolution,[],[f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 0.22/0.50    inference(nnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 0.22/0.50    inference(definition_folding,[],[f6,f15,f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X3,X1,X0] : (sP0(X3,X1,X0) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.22/0.50  fof(f224,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~sP0(X0,k1_xboole_0,X1)) ) | ~spl9_12),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f132,f50])).
% 0.22/0.50  % (23624)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X1) | ~sP0(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & ((k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) = X0 & r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X2)) | ~sP0(X0,X1,X2)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f30,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) => (k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) = X0 & r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X2)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) | ~sP0(X0,X1,X2)))),
% 0.22/0.50    inference(rectify,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X3,X1,X0] : ((sP0(X3,X1,X0) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~sP0(X3,X1,X0)))),
% 0.22/0.50    inference(nnf_transformation,[],[f14])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl9_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f131])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    spl9_12 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.22/0.50  fof(f386,plain,(
% 0.22/0.50    k1_xboole_0 != k2_zfmisc_1(sK2,k1_xboole_0) | (spl9_1 | ~spl9_2)),
% 0.22/0.50    inference(backward_demodulation,[],[f63,f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    k1_xboole_0 = sK3 | ~spl9_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    spl9_2 <=> k1_xboole_0 = sK3),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    k1_xboole_0 != k2_zfmisc_1(sK2,sK3) | spl9_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f61])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    spl9_1 <=> k1_xboole_0 = k2_zfmisc_1(sK2,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.50  fof(f372,plain,(
% 0.22/0.50    spl9_1 | ~spl9_3 | ~spl9_12),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f371])).
% 0.22/0.50  fof(f371,plain,(
% 0.22/0.50    $false | (spl9_1 | ~spl9_3 | ~spl9_12)),
% 0.22/0.50    inference(subsumption_resolution,[],[f370,f279])).
% 0.22/0.50  fof(f279,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) ) | ~spl9_12),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f260,f41])).
% 0.22/0.50  fof(f260,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))) ) | ~spl9_12),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f210,f59,f45])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~sP0(X0,X1,k1_xboole_0)) ) | ~spl9_12),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f132,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X2) | ~sP0(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f370,plain,(
% 0.22/0.50    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | (spl9_1 | ~spl9_3)),
% 0.22/0.50    inference(forward_demodulation,[],[f63,f71])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    k1_xboole_0 = sK2 | ~spl9_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f70])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    spl9_3 <=> k1_xboole_0 = sK2),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.50  fof(f357,plain,(
% 0.22/0.50    ~spl9_6 | ~spl9_8 | ~spl9_9 | ~spl9_12),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f356])).
% 0.22/0.50  fof(f356,plain,(
% 0.22/0.50    $false | (~spl9_6 | ~spl9_8 | ~spl9_9 | ~spl9_12)),
% 0.22/0.50    inference(subsumption_resolution,[],[f341,f266])).
% 0.22/0.50  fof(f266,plain,(
% 0.22/0.50    ( ! [X0] : (~sP0(X0,sK3,sK2)) ) | (~spl9_9 | ~spl9_12)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f132,f109,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X4,X1,X0) | r2_hidden(X4,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    sP1(sK2,sK3,k1_xboole_0) | ~spl9_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f107])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    spl9_9 <=> sP1(sK2,sK3,k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.22/0.50  fof(f341,plain,(
% 0.22/0.50    sP0(k4_tarski(sK4(sK2),sK4(sK3)),sK3,sK2) | (~spl9_6 | ~spl9_8)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f91,f103,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X4,X2,X3,X1] : (sP0(k4_tarski(X3,X4),X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2)) )),
% 0.22/0.50    inference(equality_resolution,[],[f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2) | k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    r2_hidden(sK4(sK3),sK3) | ~spl9_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f101])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl9_8 <=> r2_hidden(sK4(sK3),sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    r2_hidden(sK4(sK2),sK2) | ~spl9_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f89])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    spl9_6 <=> r2_hidden(sK4(sK2),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    ~spl9_11),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f134])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    $false | ~spl9_11),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f121,f129])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0)) ) | ~spl9_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f128])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    spl9_11 <=> ! [X0] : ~r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f119,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    ( ! [X0] : (r1_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.50    inference(superposition,[],[f42,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    spl9_11 | spl9_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f126,f131,f128])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(superposition,[],[f44,f39])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(rectify,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    spl9_9 | ~spl9_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f105,f61,f107])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    sP1(sK2,sK3,k1_xboole_0) | ~spl9_1),
% 0.22/0.50    inference(superposition,[],[f59,f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    k1_xboole_0 = k2_zfmisc_1(sK2,sK3) | ~spl9_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f61])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    spl9_8 | spl9_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f99,f65,f101])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    r2_hidden(sK4(sK3),sK3) | spl9_2),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f67,f41])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    k1_xboole_0 != sK3 | spl9_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f65])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    spl9_6 | spl9_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f81,f70,f89])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    r2_hidden(sK4(sK2),sK2) | spl9_3),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f72,f41])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    k1_xboole_0 != sK2 | spl9_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f70])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    spl9_1 | spl9_3 | spl9_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f36,f65,f70,f61])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK2,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ((k1_xboole_0 != sK3 & k1_xboole_0 != sK2) | k1_xboole_0 != k2_zfmisc_1(sK2,sK3)) & (k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK2,sK3))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK3 & k1_xboole_0 != sK2) | k1_xboole_0 != k2_zfmisc_1(sK2,sK3)) & (k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK2,sK3)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.50    inference(nnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.50    inference(negated_conjecture,[],[f8])).
% 0.22/0.50  fof(f8,conjecture,(
% 0.22/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ~spl9_1 | ~spl9_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f37,f70,f61])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    k1_xboole_0 != sK2 | k1_xboole_0 != k2_zfmisc_1(sK2,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ~spl9_1 | ~spl9_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f38,f65,f61])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    k1_xboole_0 != sK3 | k1_xboole_0 != k2_zfmisc_1(sK2,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (23638)------------------------------
% 0.22/0.50  % (23638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (23638)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (23638)Memory used [KB]: 10746
% 0.22/0.50  % (23638)Time elapsed: 0.080 s
% 0.22/0.50  % (23638)------------------------------
% 0.22/0.50  % (23638)------------------------------
% 0.22/0.51  % (23626)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (23621)Success in time 0.147 s
%------------------------------------------------------------------------------
