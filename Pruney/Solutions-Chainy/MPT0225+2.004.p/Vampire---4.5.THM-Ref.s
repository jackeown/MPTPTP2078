%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:06 EST 2020

% Result     : Theorem 1.77s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 160 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :  314 ( 467 expanded)
%              Number of equality atoms :  156 ( 230 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1160,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f96,f1120,f1137,f1144,f1158])).

fof(f1158,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f1157])).

fof(f1157,plain,
    ( $false
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f1151,f162])).

fof(f162,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f110,f84])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f110,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | r1_xboole_0(k1_xboole_0,X4) ) ),
    inference(superposition,[],[f66,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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

fof(f66,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f1151,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_5 ),
    inference(superposition,[],[f418,f117])).

fof(f117,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl5_5
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f418,plain,(
    ! [X27] : ~ r1_xboole_0(k1_tarski(X27),k1_tarski(X27)) ),
    inference(resolution,[],[f284,f135])).

fof(f135,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f132,f67])).

fof(f67,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f132,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f82,f74])).

fof(f74,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f82,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f35,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f284,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f129,f84])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f72,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f1144,plain,
    ( spl5_5
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f1143,f92,f88,f116])).

fof(f88,plain,
    ( spl5_1
  <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f92,plain,
    ( spl5_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1143,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f1142,f193])).

fof(f193,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f137,f178])).

fof(f178,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f171,f84])).

fof(f171,plain,(
    ! [X1] :
      ( k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)
      | ~ r1_tarski(X1,X1) ) ),
    inference(superposition,[],[f137,f55])).

fof(f137,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f61,f65])).

fof(f65,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f1142,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f89,f94])).

fof(f94,plain,
    ( sK0 = sK1
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f89,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f1137,plain,
    ( spl5_2
    | spl5_9 ),
    inference(avatar_split_clause,[],[f1133,f1117,f92])).

fof(f1117,plain,
    ( spl5_9
  <=> r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f1133,plain,
    ( sK0 = sK1
    | spl5_9 ),
    inference(resolution,[],[f1119,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f1119,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f1117])).

fof(f1120,plain,
    ( ~ spl5_9
    | spl5_1 ),
    inference(avatar_split_clause,[],[f1115,f88,f1117])).

fof(f1115,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl5_1 ),
    inference(trivial_inequality_removal,[],[f1090])).

fof(f1090,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl5_1 ),
    inference(superposition,[],[f90,f583])).

fof(f583,plain,(
    ! [X12,X11] :
      ( k4_xboole_0(X11,X12) = X11
      | ~ r1_xboole_0(X11,X12) ) ),
    inference(forward_demodulation,[],[f565,f203])).

fof(f203,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f198,f65])).

fof(f198,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f75,f178])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f565,plain,(
    ! [X12,X11] :
      ( k4_xboole_0(X11,X12) = k5_xboole_0(X11,k1_xboole_0)
      | ~ r1_xboole_0(X11,X12) ) ),
    inference(superposition,[],[f75,f238])).

fof(f238,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f127,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k3_xboole_0(X0,X1),X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f72,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f90,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f96,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f44,f92,f88])).

fof(f44,plain,
    ( sK0 != sK1
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( sK0 = sK1
      | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) )
    & ( sK0 != sK1
      | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ( X0 = X1
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
        & ( X0 != X1
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) )
   => ( ( sK0 = sK1
        | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) )
      & ( sK0 != sK1
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( X0 = X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
      & ( X0 != X1
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f95,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f45,f92,f88])).

fof(f45,plain,
    ( sK0 = sK1
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (2511)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (2528)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.51  % (2509)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (2518)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (2518)Refutation not found, incomplete strategy% (2518)------------------------------
% 0.20/0.52  % (2518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (2518)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (2518)Memory used [KB]: 6140
% 0.20/0.52  % (2518)Time elapsed: 0.103 s
% 0.20/0.52  % (2518)------------------------------
% 0.20/0.52  % (2518)------------------------------
% 0.20/0.52  % (2520)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (2510)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (2530)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (2517)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (2523)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (2512)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (2522)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (2507)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (2506)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (2507)Refutation not found, incomplete strategy% (2507)------------------------------
% 0.20/0.53  % (2507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2526)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (2529)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (2524)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (2507)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (2507)Memory used [KB]: 1663
% 0.20/0.54  % (2507)Time elapsed: 0.117 s
% 0.20/0.54  % (2507)------------------------------
% 0.20/0.54  % (2507)------------------------------
% 0.20/0.54  % (2535)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (2513)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (2531)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (2508)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (2516)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (2515)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (2532)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (2531)Refutation not found, incomplete strategy% (2531)------------------------------
% 0.20/0.55  % (2531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (2531)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (2531)Memory used [KB]: 10618
% 0.20/0.55  % (2531)Time elapsed: 0.134 s
% 0.20/0.55  % (2531)------------------------------
% 0.20/0.55  % (2531)------------------------------
% 0.20/0.55  % (2524)Refutation not found, incomplete strategy% (2524)------------------------------
% 0.20/0.55  % (2524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (2524)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (2524)Memory used [KB]: 1663
% 0.20/0.55  % (2524)Time elapsed: 0.144 s
% 0.20/0.55  % (2524)------------------------------
% 0.20/0.55  % (2524)------------------------------
% 0.20/0.55  % (2523)Refutation not found, incomplete strategy% (2523)------------------------------
% 0.20/0.55  % (2523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (2523)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (2523)Memory used [KB]: 10618
% 0.20/0.55  % (2523)Time elapsed: 0.132 s
% 0.20/0.55  % (2523)------------------------------
% 0.20/0.55  % (2523)------------------------------
% 0.20/0.55  % (2537)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (2534)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.55  % (2537)Refutation not found, incomplete strategy% (2537)------------------------------
% 0.20/0.55  % (2537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (2537)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (2537)Memory used [KB]: 1663
% 0.20/0.55  % (2537)Time elapsed: 0.001 s
% 0.20/0.55  % (2537)------------------------------
% 0.20/0.55  % (2537)------------------------------
% 0.20/0.55  % (2534)Refutation not found, incomplete strategy% (2534)------------------------------
% 0.20/0.55  % (2534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (2534)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (2534)Memory used [KB]: 6268
% 0.20/0.55  % (2525)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (2534)Time elapsed: 0.147 s
% 0.20/0.55  % (2534)------------------------------
% 0.20/0.55  % (2534)------------------------------
% 0.20/0.55  % (2519)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.56  % (2519)Refutation not found, incomplete strategy% (2519)------------------------------
% 0.20/0.56  % (2519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (2527)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.56  % (2521)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.56  % (2521)Refutation not found, incomplete strategy% (2521)------------------------------
% 0.20/0.56  % (2521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (2521)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (2521)Memory used [KB]: 1663
% 0.20/0.56  % (2521)Time elapsed: 0.156 s
% 0.20/0.56  % (2521)------------------------------
% 0.20/0.56  % (2521)------------------------------
% 0.20/0.56  % (2533)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (2533)Refutation not found, incomplete strategy% (2533)------------------------------
% 0.20/0.56  % (2533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (2519)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (2519)Memory used [KB]: 10618
% 0.20/0.57  % (2519)Time elapsed: 0.151 s
% 0.20/0.57  % (2519)------------------------------
% 0.20/0.57  % (2519)------------------------------
% 1.61/0.57  % (2533)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  
% 1.61/0.57  % (2533)Memory used [KB]: 6268
% 1.61/0.57  % (2533)Time elapsed: 0.157 s
% 1.61/0.57  % (2533)------------------------------
% 1.61/0.57  % (2533)------------------------------
% 1.61/0.57  % (2525)Refutation not found, incomplete strategy% (2525)------------------------------
% 1.61/0.57  % (2525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (2525)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  
% 1.61/0.57  % (2525)Memory used [KB]: 1663
% 1.61/0.57  % (2525)Time elapsed: 0.168 s
% 1.61/0.57  % (2525)------------------------------
% 1.61/0.57  % (2525)------------------------------
% 1.77/0.59  % (2528)Refutation found. Thanks to Tanya!
% 1.77/0.59  % SZS status Theorem for theBenchmark
% 1.77/0.59  % SZS output start Proof for theBenchmark
% 1.77/0.59  fof(f1160,plain,(
% 1.77/0.59    $false),
% 1.77/0.59    inference(avatar_sat_refutation,[],[f95,f96,f1120,f1137,f1144,f1158])).
% 1.77/0.59  fof(f1158,plain,(
% 1.77/0.59    ~spl5_5),
% 1.77/0.59    inference(avatar_contradiction_clause,[],[f1157])).
% 1.77/0.59  fof(f1157,plain,(
% 1.77/0.59    $false | ~spl5_5),
% 1.77/0.59    inference(subsumption_resolution,[],[f1151,f162])).
% 1.77/0.59  fof(f162,plain,(
% 1.77/0.59    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.77/0.59    inference(resolution,[],[f110,f84])).
% 1.77/0.59  fof(f84,plain,(
% 1.77/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.77/0.59    inference(equality_resolution,[],[f57])).
% 1.77/0.59  fof(f57,plain,(
% 1.77/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.77/0.59    inference(cnf_transformation,[],[f39])).
% 1.77/0.59  fof(f39,plain,(
% 1.77/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.77/0.59    inference(flattening,[],[f38])).
% 1.77/0.59  fof(f38,plain,(
% 1.77/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.77/0.59    inference(nnf_transformation,[],[f4])).
% 1.77/0.59  fof(f4,axiom,(
% 1.77/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.77/0.59  fof(f110,plain,(
% 1.77/0.59    ( ! [X4,X3] : (~r1_tarski(X3,X4) | r1_xboole_0(k1_xboole_0,X4)) )),
% 1.77/0.59    inference(superposition,[],[f66,f55])).
% 1.77/0.59  fof(f55,plain,(
% 1.77/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f37])).
% 1.77/0.59  fof(f37,plain,(
% 1.77/0.59    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.77/0.59    inference(nnf_transformation,[],[f5])).
% 1.77/0.59  fof(f5,axiom,(
% 1.77/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.77/0.59  fof(f66,plain,(
% 1.77/0.59    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f11])).
% 1.77/0.59  fof(f11,axiom,(
% 1.77/0.59    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.77/0.59  fof(f1151,plain,(
% 1.77/0.59    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_5),
% 1.77/0.59    inference(superposition,[],[f418,f117])).
% 1.77/0.59  fof(f117,plain,(
% 1.77/0.59    k1_xboole_0 = k1_tarski(sK0) | ~spl5_5),
% 1.77/0.59    inference(avatar_component_clause,[],[f116])).
% 1.77/0.59  fof(f116,plain,(
% 1.77/0.59    spl5_5 <=> k1_xboole_0 = k1_tarski(sK0)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.77/0.59  fof(f418,plain,(
% 1.77/0.59    ( ! [X27] : (~r1_xboole_0(k1_tarski(X27),k1_tarski(X27))) )),
% 1.77/0.59    inference(resolution,[],[f284,f135])).
% 1.77/0.59  fof(f135,plain,(
% 1.77/0.59    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 1.77/0.59    inference(superposition,[],[f132,f67])).
% 1.77/0.59  fof(f67,plain,(
% 1.77/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f13])).
% 1.77/0.59  fof(f13,axiom,(
% 1.77/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.77/0.59  fof(f132,plain,(
% 1.77/0.59    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 1.77/0.59    inference(superposition,[],[f82,f74])).
% 1.77/0.59  fof(f74,plain,(
% 1.77/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f14])).
% 1.77/0.59  fof(f14,axiom,(
% 1.77/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.77/0.59  fof(f82,plain,(
% 1.77/0.59    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 1.77/0.59    inference(equality_resolution,[],[f81])).
% 1.77/0.59  fof(f81,plain,(
% 1.77/0.59    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 1.77/0.59    inference(equality_resolution,[],[f47])).
% 1.77/0.59  fof(f47,plain,(
% 1.77/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.77/0.59    inference(cnf_transformation,[],[f36])).
% 1.77/0.59  fof(f36,plain,(
% 1.77/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.77/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 1.77/0.59  fof(f35,plain,(
% 1.77/0.59    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 1.77/0.59    introduced(choice_axiom,[])).
% 1.77/0.60  fof(f34,plain,(
% 1.77/0.60    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.77/0.60    inference(rectify,[],[f33])).
% 1.77/0.60  fof(f33,plain,(
% 1.77/0.60    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.77/0.60    inference(flattening,[],[f32])).
% 1.77/0.60  fof(f32,plain,(
% 1.77/0.60    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.77/0.60    inference(nnf_transformation,[],[f23])).
% 1.77/0.60  fof(f23,plain,(
% 1.77/0.60    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.77/0.60    inference(ennf_transformation,[],[f12])).
% 1.77/0.60  fof(f12,axiom,(
% 1.77/0.60    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.77/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.77/0.60  fof(f284,plain,(
% 1.77/0.60    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r1_xboole_0(X0,X0)) )),
% 1.77/0.60    inference(resolution,[],[f129,f84])).
% 1.77/0.60  fof(f129,plain,(
% 1.77/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.77/0.60    inference(superposition,[],[f72,f59])).
% 1.77/0.60  fof(f59,plain,(
% 1.77/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.77/0.60    inference(cnf_transformation,[],[f24])).
% 1.77/0.60  fof(f24,plain,(
% 1.77/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.77/0.60    inference(ennf_transformation,[],[f7])).
% 1.77/0.60  fof(f7,axiom,(
% 1.77/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.77/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.77/0.60  fof(f72,plain,(
% 1.77/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.77/0.60    inference(cnf_transformation,[],[f43])).
% 1.77/0.60  fof(f43,plain,(
% 1.77/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.77/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f42])).
% 1.77/0.60  fof(f42,plain,(
% 1.77/0.60    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.77/0.60    introduced(choice_axiom,[])).
% 1.77/0.60  fof(f28,plain,(
% 1.77/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.77/0.60    inference(ennf_transformation,[],[f21])).
% 1.77/0.60  fof(f21,plain,(
% 1.77/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.77/0.60    inference(rectify,[],[f3])).
% 1.77/0.60  fof(f3,axiom,(
% 1.77/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.77/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.77/0.60  fof(f1144,plain,(
% 1.77/0.60    spl5_5 | ~spl5_1 | ~spl5_2),
% 1.77/0.60    inference(avatar_split_clause,[],[f1143,f92,f88,f116])).
% 1.77/0.60  fof(f88,plain,(
% 1.77/0.60    spl5_1 <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.77/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.77/0.60  fof(f92,plain,(
% 1.77/0.60    spl5_2 <=> sK0 = sK1),
% 1.77/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.77/0.60  fof(f1143,plain,(
% 1.77/0.60    k1_xboole_0 = k1_tarski(sK0) | (~spl5_1 | ~spl5_2)),
% 1.77/0.60    inference(forward_demodulation,[],[f1142,f193])).
% 1.77/0.60  fof(f193,plain,(
% 1.77/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.77/0.60    inference(backward_demodulation,[],[f137,f178])).
% 1.77/0.60  fof(f178,plain,(
% 1.77/0.60    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 1.77/0.60    inference(subsumption_resolution,[],[f171,f84])).
% 1.77/0.60  fof(f171,plain,(
% 1.77/0.60    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) | ~r1_tarski(X1,X1)) )),
% 1.77/0.60    inference(superposition,[],[f137,f55])).
% 1.77/0.60  fof(f137,plain,(
% 1.77/0.60    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 1.77/0.60    inference(superposition,[],[f61,f65])).
% 1.77/0.60  fof(f65,plain,(
% 1.77/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.77/0.60    inference(cnf_transformation,[],[f8])).
% 1.77/0.60  fof(f8,axiom,(
% 1.77/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.77/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.77/0.60  fof(f61,plain,(
% 1.77/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.77/0.60    inference(cnf_transformation,[],[f9])).
% 1.77/0.60  fof(f9,axiom,(
% 1.77/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.77/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.77/0.60  fof(f1142,plain,(
% 1.77/0.60    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | (~spl5_1 | ~spl5_2)),
% 1.77/0.60    inference(forward_demodulation,[],[f89,f94])).
% 1.77/0.60  fof(f94,plain,(
% 1.77/0.60    sK0 = sK1 | ~spl5_2),
% 1.77/0.60    inference(avatar_component_clause,[],[f92])).
% 1.77/0.60  fof(f89,plain,(
% 1.77/0.60    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~spl5_1),
% 1.77/0.60    inference(avatar_component_clause,[],[f88])).
% 1.77/0.60  fof(f1137,plain,(
% 1.77/0.60    spl5_2 | spl5_9),
% 1.77/0.60    inference(avatar_split_clause,[],[f1133,f1117,f92])).
% 1.77/0.60  fof(f1117,plain,(
% 1.77/0.60    spl5_9 <=> r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.77/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.77/0.60  fof(f1133,plain,(
% 1.77/0.60    sK0 = sK1 | spl5_9),
% 1.77/0.60    inference(resolution,[],[f1119,f60])).
% 1.77/0.60  fof(f60,plain,(
% 1.77/0.60    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.77/0.60    inference(cnf_transformation,[],[f25])).
% 1.77/0.60  fof(f25,plain,(
% 1.77/0.60    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 1.77/0.60    inference(ennf_transformation,[],[f17])).
% 1.77/0.60  fof(f17,axiom,(
% 1.77/0.60    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.77/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 1.77/0.60  fof(f1119,plain,(
% 1.77/0.60    ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl5_9),
% 1.77/0.60    inference(avatar_component_clause,[],[f1117])).
% 1.77/0.60  fof(f1120,plain,(
% 1.77/0.60    ~spl5_9 | spl5_1),
% 1.77/0.60    inference(avatar_split_clause,[],[f1115,f88,f1117])).
% 1.77/0.60  fof(f1115,plain,(
% 1.77/0.60    ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl5_1),
% 1.77/0.60    inference(trivial_inequality_removal,[],[f1090])).
% 1.77/0.60  fof(f1090,plain,(
% 1.77/0.60    k1_tarski(sK0) != k1_tarski(sK0) | ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl5_1),
% 1.77/0.60    inference(superposition,[],[f90,f583])).
% 1.77/0.60  fof(f583,plain,(
% 1.77/0.60    ( ! [X12,X11] : (k4_xboole_0(X11,X12) = X11 | ~r1_xboole_0(X11,X12)) )),
% 1.77/0.60    inference(forward_demodulation,[],[f565,f203])).
% 1.77/0.60  fof(f203,plain,(
% 1.77/0.60    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = X1) )),
% 1.77/0.60    inference(forward_demodulation,[],[f198,f65])).
% 1.77/0.60  fof(f198,plain,(
% 1.77/0.60    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k1_xboole_0)) )),
% 1.77/0.60    inference(superposition,[],[f75,f178])).
% 1.77/0.60  fof(f75,plain,(
% 1.77/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.77/0.60    inference(cnf_transformation,[],[f6])).
% 1.77/0.60  fof(f6,axiom,(
% 1.77/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.77/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.77/0.60  fof(f565,plain,(
% 1.77/0.60    ( ! [X12,X11] : (k4_xboole_0(X11,X12) = k5_xboole_0(X11,k1_xboole_0) | ~r1_xboole_0(X11,X12)) )),
% 1.77/0.60    inference(superposition,[],[f75,f238])).
% 1.77/0.60  fof(f238,plain,(
% 1.77/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.77/0.60    inference(resolution,[],[f127,f64])).
% 1.77/0.60  fof(f64,plain,(
% 1.77/0.60    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.77/0.60    inference(cnf_transformation,[],[f26])).
% 1.77/0.60  fof(f26,plain,(
% 1.77/0.60    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.77/0.60    inference(ennf_transformation,[],[f10])).
% 1.77/0.60  fof(f10,axiom,(
% 1.77/0.60    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.77/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.77/0.60  fof(f127,plain,(
% 1.77/0.60    ( ! [X2,X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),X2) | ~r1_xboole_0(X0,X1)) )),
% 1.77/0.60    inference(resolution,[],[f72,f68])).
% 1.77/0.60  fof(f68,plain,(
% 1.77/0.60    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.77/0.60    inference(cnf_transformation,[],[f41])).
% 1.77/0.60  fof(f41,plain,(
% 1.77/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.77/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f40])).
% 1.77/0.60  fof(f40,plain,(
% 1.77/0.60    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.77/0.60    introduced(choice_axiom,[])).
% 1.77/0.60  fof(f27,plain,(
% 1.77/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.77/0.60    inference(ennf_transformation,[],[f20])).
% 1.77/0.60  fof(f20,plain,(
% 1.77/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.77/0.60    inference(rectify,[],[f2])).
% 1.77/0.60  fof(f2,axiom,(
% 1.77/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.77/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.77/0.60  fof(f90,plain,(
% 1.77/0.60    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl5_1),
% 1.77/0.60    inference(avatar_component_clause,[],[f88])).
% 1.77/0.60  fof(f96,plain,(
% 1.77/0.60    spl5_1 | ~spl5_2),
% 1.77/0.60    inference(avatar_split_clause,[],[f44,f92,f88])).
% 1.77/0.60  fof(f44,plain,(
% 1.77/0.60    sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.77/0.60    inference(cnf_transformation,[],[f31])).
% 1.77/0.60  fof(f31,plain,(
% 1.77/0.60    (sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) & (sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.77/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f30])).
% 1.77/0.60  fof(f30,plain,(
% 1.77/0.60    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) => ((sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) & (sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))),
% 1.77/0.60    introduced(choice_axiom,[])).
% 1.77/0.60  fof(f29,plain,(
% 1.77/0.60    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.77/0.60    inference(nnf_transformation,[],[f22])).
% 1.77/0.60  fof(f22,plain,(
% 1.77/0.60    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <~> X0 != X1)),
% 1.77/0.60    inference(ennf_transformation,[],[f19])).
% 1.77/0.60  fof(f19,negated_conjecture,(
% 1.77/0.60    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.77/0.60    inference(negated_conjecture,[],[f18])).
% 1.77/0.60  fof(f18,conjecture,(
% 1.77/0.60    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.77/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.77/0.60  fof(f95,plain,(
% 1.77/0.60    ~spl5_1 | spl5_2),
% 1.77/0.60    inference(avatar_split_clause,[],[f45,f92,f88])).
% 1.77/0.60  fof(f45,plain,(
% 1.77/0.60    sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.77/0.60    inference(cnf_transformation,[],[f31])).
% 1.77/0.60  % SZS output end Proof for theBenchmark
% 1.77/0.60  % (2528)------------------------------
% 1.77/0.60  % (2528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.60  % (2528)Termination reason: Refutation
% 1.77/0.60  
% 1.77/0.60  % (2528)Memory used [KB]: 6780
% 1.77/0.60  % (2528)Time elapsed: 0.194 s
% 1.77/0.60  % (2528)------------------------------
% 1.77/0.60  % (2528)------------------------------
% 1.77/0.60  % (2503)Success in time 0.251 s
%------------------------------------------------------------------------------
