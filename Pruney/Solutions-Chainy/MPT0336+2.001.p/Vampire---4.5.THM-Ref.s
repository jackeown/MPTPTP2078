%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:23 EST 2020

% Result     : Theorem 7.57s
% Output     : Refutation 7.57s
% Verified   : 
% Statistics : Number of formulae       :  259 (2165 expanded)
%              Number of leaves         :   51 ( 741 expanded)
%              Depth                    :   30
%              Number of atoms          :  651 (3741 expanded)
%              Number of equality atoms :   92 (1825 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15020,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f137,f141,f145,f149,f163,f176,f187,f193,f1232,f1264,f1285,f4278,f4504,f6025,f9454,f9496,f9629,f14046,f14125,f14469,f14612,f15019])).

fof(f15019,plain,
    ( ~ spl8_89
    | ~ spl8_108 ),
    inference(avatar_contradiction_clause,[],[f15018])).

fof(f15018,plain,
    ( $false
    | ~ spl8_89
    | ~ spl8_108 ),
    inference(subsumption_resolution,[],[f14592,f15003])).

fof(f15003,plain,
    ( ! [X0] : ~ r2_hidden(sK3,k4_xboole_0(X0,k4_xboole_0(X0,sK1)))
    | ~ spl8_89 ),
    inference(superposition,[],[f14947,f112])).

fof(f112,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f64,f71,f71])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f14947,plain,
    ( ! [X3] : ~ r2_hidden(sK3,k4_xboole_0(sK1,k4_xboole_0(sK1,X3)))
    | ~ spl8_89 ),
    inference(resolution,[],[f9452,f687])).

fof(f687,plain,(
    ! [X14,X12,X13] :
      ( r2_hidden(X14,k5_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),k4_xboole_0(X12,X13)))
      | ~ r2_hidden(X14,k4_xboole_0(X12,k4_xboole_0(X12,X13))) ) ),
    inference(superposition,[],[f157,f115])).

fof(f115,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f157,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(forward_demodulation,[],[f132,f113])).

fof(f113,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f67,f105])).

fof(f105,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f66,f104])).

fof(f104,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f65,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f86,f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f96,f101])).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f97,f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f98,f99])).

fof(f99,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f96,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f86,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f132,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f126])).

fof(f126,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f88,f105])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
              & ~ r2_hidden(sK7(X0,X1,X2),X0) )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( r2_hidden(sK7(X0,X1,X2),X1)
            | r2_hidden(sK7(X0,X1,X2),X0)
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f51,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            & ~ r2_hidden(sK7(X0,X1,X2),X0) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( r2_hidden(sK7(X0,X1,X2),X1)
          | r2_hidden(sK7(X0,X1,X2),X0)
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f9452,plain,
    ( ! [X5] : ~ r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X5)),k4_xboole_0(sK1,X5)))
    | ~ spl8_89 ),
    inference(avatar_component_clause,[],[f9451])).

fof(f9451,plain,
    ( spl8_89
  <=> ! [X5] : ~ r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X5)),k4_xboole_0(sK1,X5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).

fof(f14592,plain,
    ( r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl8_108 ),
    inference(avatar_component_clause,[],[f14591])).

fof(f14591,plain,
    ( spl8_108
  <=> r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_108])])).

fof(f14612,plain,
    ( spl8_108
    | ~ spl8_100 ),
    inference(avatar_split_clause,[],[f14611,f14121,f14591])).

fof(f14121,plain,
    ( spl8_100
  <=> ! [X0] : r2_hidden(sK3,k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_100])])).

fof(f14611,plain,
    ( r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl8_100 ),
    inference(forward_demodulation,[],[f14587,f61])).

fof(f61,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f14587,plain,
    ( r2_hidden(sK3,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0))
    | ~ spl8_100 ),
    inference(superposition,[],[f14122,f5041])).

fof(f5041,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(forward_demodulation,[],[f5039,f61])).

fof(f5039,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(superposition,[],[f2680,f113])).

fof(f2680,plain,(
    ! [X1] : k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(forward_demodulation,[],[f2664,f61])).

fof(f2664,plain,(
    ! [X1] : k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(X1,k1_xboole_0))) = X1 ),
    inference(superposition,[],[f152,f110])).

fof(f110,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f60,f71])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f152,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(forward_demodulation,[],[f116,f111])).

fof(f111,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f63,f104,f104])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f116,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f72,f105,f71])).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f14122,plain,
    ( ! [X0] : r2_hidden(sK3,k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0)))
    | ~ spl8_100 ),
    inference(avatar_component_clause,[],[f14121])).

fof(f14469,plain,
    ( ~ spl8_66
    | ~ spl8_88
    | ~ spl8_94 ),
    inference(avatar_split_clause,[],[f14465,f14044,f6023,f4497])).

fof(f4497,plain,
    ( spl8_66
  <=> r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f6023,plain,
    ( spl8_88
  <=> r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).

fof(f14044,plain,
    ( spl8_94
  <=> ! [X23] :
        ( ~ r2_hidden(X23,sK1)
        | ~ r2_hidden(X23,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_94])])).

fof(f14465,plain,
    ( ~ r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),sK1)
    | ~ spl8_88
    | ~ spl8_94 ),
    inference(resolution,[],[f14045,f6024])).

fof(f6024,plain,
    ( r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),sK0)
    | ~ spl8_88 ),
    inference(avatar_component_clause,[],[f6023])).

fof(f14045,plain,
    ( ! [X23] :
        ( ~ r2_hidden(X23,sK0)
        | ~ r2_hidden(X23,sK1) )
    | ~ spl8_94 ),
    inference(avatar_component_clause,[],[f14044])).

fof(f14125,plain,
    ( spl8_94
    | spl8_100
    | ~ spl8_92 ),
    inference(avatar_split_clause,[],[f14098,f14036,f14121,f14044])).

fof(f14036,plain,
    ( spl8_92
  <=> ! [X19] :
        ( r2_hidden(sK3,X19)
        | ~ r2_hidden(sK4(sK0,sK1),X19) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f14098,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK3,k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X3)))
        | ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X4,sK0) )
    | ~ spl8_92 ),
    inference(resolution,[],[f14061,f937])).

fof(f937,plain,(
    ! [X6,X7,X5] :
      ( r2_hidden(sK4(X5,X6),k4_xboole_0(X5,k4_xboole_0(X5,X6)))
      | ~ r2_hidden(X7,X6)
      | ~ r2_hidden(X7,X5) ) ),
    inference(resolution,[],[f118,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
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

fof(f118,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f73,f71])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f14061,plain,
    ( ! [X12,X11] :
        ( ~ r2_hidden(sK4(sK0,sK1),X11)
        | r2_hidden(sK3,k5_xboole_0(X12,k4_xboole_0(X11,X12))) )
    | ~ spl8_92 ),
    inference(resolution,[],[f14037,f156])).

fof(f156,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) ),
    inference(forward_demodulation,[],[f131,f113])).

fof(f131,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f89,f105])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f14037,plain,
    ( ! [X19] :
        ( r2_hidden(sK3,X19)
        | ~ r2_hidden(sK4(sK0,sK1),X19) )
    | ~ spl8_92 ),
    inference(avatar_component_clause,[],[f14036])).

fof(f14046,plain,
    ( spl8_94
    | spl8_92
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f14026,f147,f14036,f14044])).

fof(f147,plain,
    ( spl8_4
  <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f14026,plain,
    ( ! [X23,X22] :
        ( r2_hidden(sK3,X22)
        | ~ r2_hidden(sK4(sK0,sK1),X22)
        | ~ r2_hidden(X23,sK1)
        | ~ r2_hidden(X23,sK0) )
    | ~ spl8_4 ),
    inference(resolution,[],[f13992,f937])).

fof(f13992,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
        | r2_hidden(sK3,X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl8_4 ),
    inference(resolution,[],[f1327,f196])).

fof(f196,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
        | ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) )
    | ~ spl8_4 ),
    inference(resolution,[],[f79,f148])).

fof(f148,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f147])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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

fof(f1327,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X7,k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5))
      | ~ r2_hidden(X7,X6)
      | r2_hidden(X5,X6) ) ),
    inference(resolution,[],[f119,f77])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f78,f106])).

fof(f106,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f62,f104])).

fof(f62,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f9629,plain,
    ( ~ spl8_58
    | spl8_31 ),
    inference(avatar_split_clause,[],[f9628,f1227,f3519])).

fof(f3519,plain,
    ( spl8_58
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f1227,plain,
    ( spl8_31
  <=> r2_hidden(sK3,k5_xboole_0(k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f9628,plain,
    ( ~ r2_hidden(sK3,sK1)
    | spl8_31 ),
    inference(forward_demodulation,[],[f1228,f5041])).

fof(f1228,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(k1_xboole_0,sK1))
    | spl8_31 ),
    inference(avatar_component_clause,[],[f1227])).

fof(f9496,plain,
    ( ~ spl8_2
    | ~ spl8_9
    | ~ spl8_34 ),
    inference(avatar_contradiction_clause,[],[f9494])).

fof(f9494,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_9
    | ~ spl8_34 ),
    inference(resolution,[],[f1260,f203])).

fof(f203,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl8_2
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f202,f164])).

fof(f164,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f110,f61])).

fof(f202,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK1,sK1))
    | ~ spl8_2
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f201,f192])).

fof(f192,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl8_9
  <=> sK1 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f201,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f198,f112])).

fof(f198,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))
    | ~ spl8_2 ),
    inference(resolution,[],[f117,f140])).

fof(f140,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl8_2
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f74,f71])).

% (16095)Termination reason: Time limit
fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1260,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f1259])).

fof(f1259,plain,
    ( spl8_34
  <=> r2_hidden(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f9454,plain,
    ( spl8_89
    | spl8_58
    | spl8_37 ),
    inference(avatar_split_clause,[],[f9449,f1283,f3519,f9451])).

fof(f1283,plain,
    ( spl8_37
  <=> r2_hidden(sK3,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f9449,plain,
    ( ! [X5] :
        ( r2_hidden(sK3,sK1)
        | ~ r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X5)),k4_xboole_0(sK1,X5))) )
    | spl8_37 ),
    inference(forward_demodulation,[],[f9448,f8586])).

fof(f8586,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2 ),
    inference(superposition,[],[f2677,f151])).

fof(f151,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(forward_demodulation,[],[f150,f113])).

fof(f150,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(forward_demodulation,[],[f114,f113])).

fof(f114,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f68,f105,f105])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f2677,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X2,X3))) = X2 ),
    inference(superposition,[],[f152,f113])).

fof(f9448,plain,
    ( ! [X5] :
        ( r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X5)),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X5)))))
        | ~ r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X5)),k4_xboole_0(sK1,X5))) )
    | spl8_37 ),
    inference(forward_demodulation,[],[f9425,f112])).

fof(f9425,plain,
    ( ! [X5] :
        ( r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X5)),k4_xboole_0(k4_xboole_0(sK1,X5),k4_xboole_0(k4_xboole_0(sK1,X5),sK1))))
        | ~ r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X5)),k4_xboole_0(sK1,X5))) )
    | spl8_37 ),
    inference(resolution,[],[f479,f8035])).

fof(f8035,plain,
    ( ! [X0] :
        ( r2_hidden(sK3,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))
        | ~ r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,X0))) )
    | spl8_37 ),
    inference(superposition,[],[f8020,f112])).

fof(f8020,plain,
    ( ! [X0] :
        ( r2_hidden(sK3,k4_xboole_0(X0,k4_xboole_0(X0,sK1)))
        | ~ r2_hidden(sK3,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),k4_xboole_0(sK1,X0))) )
    | spl8_37 ),
    inference(forward_demodulation,[],[f8019,f115])).

fof(f8019,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))))
        | r2_hidden(sK3,k4_xboole_0(X0,k4_xboole_0(X0,sK1))) )
    | spl8_37 ),
    inference(forward_demodulation,[],[f8003,f112])).

fof(f8003,plain,
    ( ! [X0] :
        ( r2_hidden(sK3,k4_xboole_0(X0,k4_xboole_0(X0,sK1)))
        | ~ r2_hidden(sK3,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),k4_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(k4_xboole_0(sK1,X0),sK1)))) )
    | spl8_37 ),
    inference(superposition,[],[f7557,f112])).

fof(f7557,plain,
    ( ! [X211] :
        ( r2_hidden(sK3,k4_xboole_0(sK1,X211))
        | ~ r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,X211),k4_xboole_0(X211,k4_xboole_0(X211,sK1)))) )
    | spl8_37 ),
    inference(forward_demodulation,[],[f7556,f5041])).

fof(f7556,plain,
    ( ! [X211] :
        ( r2_hidden(sK3,k4_xboole_0(k5_xboole_0(k1_xboole_0,sK1),X211))
        | ~ r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,X211),k4_xboole_0(X211,k4_xboole_0(X211,sK1)))) )
    | spl8_37 ),
    inference(forward_demodulation,[],[f7555,f5041])).

fof(f7555,plain,
    ( ! [X211] :
        ( r2_hidden(sK3,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1)),X211))
        | ~ r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,X211),k4_xboole_0(X211,k4_xboole_0(X211,sK1)))) )
    | spl8_37 ),
    inference(forward_demodulation,[],[f7554,f5041])).

fof(f7554,plain,
    ( ! [X211] :
        ( r2_hidden(sK3,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))),X211))
        | ~ r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,X211),k4_xboole_0(X211,k4_xboole_0(X211,sK1)))) )
    | spl8_37 ),
    inference(forward_demodulation,[],[f7553,f681])).

fof(f681,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(superposition,[],[f115,f112])).

fof(f7553,plain,
    ( ! [X211] :
        ( ~ r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,X211),k4_xboole_0(X211,k4_xboole_0(X211,sK1))))
        | r2_hidden(sK3,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))),k4_xboole_0(X211,k4_xboole_0(X211,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))))))) )
    | spl8_37 ),
    inference(forward_demodulation,[],[f7552,f681])).

fof(f7552,plain,
    ( ! [X211] :
        ( ~ r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X211,k4_xboole_0(X211,sK1))),k4_xboole_0(X211,k4_xboole_0(X211,sK1))))
        | r2_hidden(sK3,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))),k4_xboole_0(X211,k4_xboole_0(X211,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))))))) )
    | spl8_37 ),
    inference(forward_demodulation,[],[f7551,f5041])).

fof(f7551,plain,
    ( ! [X211] :
        ( ~ r2_hidden(sK3,k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k4_xboole_0(X211,k4_xboole_0(X211,k5_xboole_0(k1_xboole_0,sK1)))),k4_xboole_0(X211,k4_xboole_0(X211,k5_xboole_0(k1_xboole_0,sK1)))))
        | r2_hidden(sK3,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))),k4_xboole_0(X211,k4_xboole_0(X211,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))))))) )
    | spl8_37 ),
    inference(forward_demodulation,[],[f7550,f5041])).

% (16095)Memory used [KB]: 13432
% (16095)Time elapsed: 0.409 s
% (16095)------------------------------
% (16095)------------------------------
fof(f7550,plain,
    ( ! [X211] :
        ( ~ r2_hidden(sK3,k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1)),k4_xboole_0(X211,k4_xboole_0(X211,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))))),k4_xboole_0(X211,k4_xboole_0(X211,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))))))
        | r2_hidden(sK3,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))),k4_xboole_0(X211,k4_xboole_0(X211,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))))))) )
    | spl8_37 ),
    inference(forward_demodulation,[],[f7148,f5041])).

fof(f7148,plain,
    ( ! [X211] :
        ( ~ r2_hidden(sK3,k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))),k4_xboole_0(X211,k4_xboole_0(X211,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1)))))),k4_xboole_0(X211,k4_xboole_0(X211,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1)))))))
        | r2_hidden(sK3,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))),k4_xboole_0(X211,k4_xboole_0(X211,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))))))) )
    | spl8_37 ),
    inference(superposition,[],[f1289,f674])).

fof(f674,plain,(
    ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))) ),
    inference(superposition,[],[f115,f112])).

fof(f1289,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))),X0)))
        | r2_hidden(sK3,X0) )
    | spl8_37 ),
    inference(resolution,[],[f1284,f158])).

fof(f158,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0)))
      | r2_hidden(X4,X0) ) ),
    inference(forward_demodulation,[],[f133,f113])).

fof(f133,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f87,f105])).

fof(f87,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1284,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))))
    | spl8_37 ),
    inference(avatar_component_clause,[],[f1283])).

fof(f479,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X7,k4_xboole_0(X5,X6))
      | r2_hidden(X7,k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,k4_xboole_0(X6,X5)))) ) ),
    inference(superposition,[],[f157,f112])).

fof(f6025,plain,
    ( spl8_7
    | spl8_88
    | ~ spl8_2
    | ~ spl8_62 ),
    inference(avatar_split_clause,[],[f6008,f4271,f139,f6023,f174])).

fof(f174,plain,
    ( spl8_7
  <=> k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f4271,plain,
    ( spl8_62
  <=> r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),k5_xboole_0(sK0,k4_xboole_0(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f6008,plain,
    ( r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),sK0)
    | k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1)
    | ~ spl8_2
    | ~ spl8_62 ),
    inference(resolution,[],[f1943,f4272])).

fof(f4272,plain,
    ( r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)))
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f4271])).

fof(f1943,plain,
    ( ! [X10,X9] :
        ( ~ r2_hidden(sK5(X9,sK1),k5_xboole_0(X10,k4_xboole_0(sK2,X10)))
        | r2_hidden(sK5(X9,sK1),X10)
        | k4_xboole_0(X9,sK1) = X9 )
    | ~ spl8_2 ),
    inference(resolution,[],[f1202,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f1202,plain,
    ( ! [X19,X20] :
        ( r1_xboole_0(X19,sK1)
        | r2_hidden(sK5(X19,sK1),X20)
        | ~ r2_hidden(sK5(X19,sK1),k5_xboole_0(X20,k4_xboole_0(sK2,X20))) )
    | ~ spl8_2 ),
    inference(resolution,[],[f158,f180])).

fof(f180,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(X1,sK1),sK2)
        | r1_xboole_0(X1,sK1) )
    | ~ spl8_2 ),
    inference(resolution,[],[f177,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl8_2 ),
    inference(resolution,[],[f77,f140])).

fof(f4504,plain,
    ( spl8_66
    | spl8_5 ),
    inference(avatar_split_clause,[],[f4503,f161,f4497])).

fof(f161,plain,
    ( spl8_5
  <=> r1_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f4503,plain,
    ( r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),sK1)
    | spl8_5 ),
    inference(forward_demodulation,[],[f4502,f61])).

fof(f4502,plain,
    ( r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),k4_xboole_0(sK1,k1_xboole_0))
    | spl8_5 ),
    inference(forward_demodulation,[],[f4485,f164])).

fof(f4485,plain,
    ( r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))
    | spl8_5 ),
    inference(superposition,[],[f4471,f685])).

fof(f685,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f107,f115])).

fof(f107,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f69,f71])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f4471,plain,
    ( ! [X0] : r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),k5_xboole_0(X0,k4_xboole_0(sK1,X0)))
    | spl8_5 ),
    inference(resolution,[],[f257,f162])).

fof(f162,plain,
    ( ~ r1_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f161])).

fof(f257,plain,(
    ! [X6,X8,X7] :
      ( r1_xboole_0(X6,X7)
      | r2_hidden(sK5(X6,X7),k5_xboole_0(X8,k4_xboole_0(X7,X8))) ) ),
    inference(resolution,[],[f156,f76])).

fof(f4278,plain,
    ( spl8_62
    | spl8_5 ),
    inference(avatar_split_clause,[],[f4277,f161,f4271])).

fof(f4277,plain,
    ( r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)))
    | spl8_5 ),
    inference(forward_demodulation,[],[f4276,f61])).

fof(f4276,plain,
    ( r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),k1_xboole_0))
    | spl8_5 ),
    inference(forward_demodulation,[],[f4263,f164])).

fof(f4263,plain,
    ( r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)))))
    | spl8_5 ),
    inference(superposition,[],[f4242,f685])).

fof(f4242,plain,
    ( ! [X0] : r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),X0)))
    | spl8_5 ),
    inference(resolution,[],[f256,f162])).

fof(f256,plain,(
    ! [X4,X5,X3] :
      ( r1_xboole_0(X3,X4)
      | r2_hidden(sK5(X3,X4),k5_xboole_0(X5,k4_xboole_0(X3,X5))) ) ),
    inference(resolution,[],[f156,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1285,plain,
    ( spl8_34
    | ~ spl8_37
    | spl8_35 ),
    inference(avatar_split_clause,[],[f1276,f1262,f1283,f1259])).

fof(f1262,plain,
    ( spl8_35
  <=> r2_hidden(sK3,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f1276,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))))
    | r2_hidden(sK3,k1_xboole_0)
    | spl8_35 ),
    inference(superposition,[],[f1268,f61])).

fof(f1268,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1)),X0)))
        | r2_hidden(sK3,X0) )
    | spl8_35 ),
    inference(resolution,[],[f1263,f158])).

fof(f1263,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1)))
    | spl8_35 ),
    inference(avatar_component_clause,[],[f1262])).

fof(f1264,plain,
    ( spl8_34
    | ~ spl8_35
    | spl8_31 ),
    inference(avatar_split_clause,[],[f1252,f1227,f1262,f1259])).

fof(f1252,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1)))
    | r2_hidden(sK3,k1_xboole_0)
    | spl8_31 ),
    inference(superposition,[],[f1237,f61])).

fof(f1237,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,sK1),X0)))
        | r2_hidden(sK3,X0) )
    | spl8_31 ),
    inference(resolution,[],[f1228,f158])).

fof(f1232,plain,
    ( ~ spl8_31
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f1231,f191,f143,f139,f1227])).

fof(f143,plain,
    ( spl8_3
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f1231,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(k1_xboole_0,sK1))
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f1230,f61])).

fof(f1230,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k1_xboole_0)))
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f1220,f213])).

fof(f213,plain,
    ( ! [X4] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4)
    | ~ spl8_2
    | ~ spl8_9 ),
    inference(resolution,[],[f208,f82])).

fof(f208,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl8_2
    | ~ spl8_9 ),
    inference(resolution,[],[f203,f75])).

fof(f1220,plain,
    ( ! [X2] : ~ r2_hidden(sK3,k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)),k4_xboole_0(sK1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)))))
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_9 ),
    inference(resolution,[],[f1214,f211])).

fof(f211,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))
    | ~ spl8_2
    | ~ spl8_9 ),
    inference(resolution,[],[f208,f117])).

fof(f1214,plain,
    ( ! [X3] :
        ( r2_hidden(sK3,X3)
        | ~ r2_hidden(sK3,k5_xboole_0(X3,k4_xboole_0(sK1,X3))) )
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(resolution,[],[f1199,f144])).

fof(f144,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f143])).

fof(f1199,plain,
    ( ! [X12,X13] :
        ( ~ r2_hidden(X12,sK2)
        | r2_hidden(X12,X13)
        | ~ r2_hidden(X12,k5_xboole_0(X13,k4_xboole_0(sK1,X13))) )
    | ~ spl8_2 ),
    inference(resolution,[],[f158,f177])).

fof(f193,plain,
    ( spl8_9
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f189,f185,f191])).

fof(f185,plain,
    ( spl8_8
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f189,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl8_8 ),
    inference(resolution,[],[f186,f82])).

fof(f186,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f185])).

fof(f187,plain,
    ( spl8_8
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f183,f139,f185])).

fof(f183,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl8_2 ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,
    ( r1_xboole_0(sK1,sK2)
    | r1_xboole_0(sK1,sK2)
    | ~ spl8_2 ),
    inference(resolution,[],[f179,f76])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK1,X0),sK2)
        | r1_xboole_0(sK1,X0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f177,f75])).

fof(f176,plain,
    ( ~ spl8_7
    | spl8_5 ),
    inference(avatar_split_clause,[],[f171,f161,f174])).

fof(f171,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1)
    | spl8_5 ),
    inference(resolution,[],[f83,f162])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f163,plain,
    ( ~ spl8_5
    | spl8_1 ),
    inference(avatar_split_clause,[],[f159,f135,f161])).

fof(f135,plain,
    ( spl8_1
  <=> r1_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f159,plain,
    ( ~ r1_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1)
    | spl8_1 ),
    inference(forward_demodulation,[],[f136,f113])).

fof(f136,plain,
    ( ~ r1_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)),sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f135])).

fof(f149,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f109,f147])).

fof(f109,plain,(
    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f56,f71,f106])).

fof(f56,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f145,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f57,f143])).

fof(f57,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f141,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f58,f139])).

fof(f58,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f137,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f108,f135])).

fof(f108,plain,(
    ~ r1_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)),sK1) ),
    inference(definition_unfolding,[],[f59,f105])).

fof(f59,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (822640641)
% 0.13/0.37  ipcrm: permission denied for id (822870027)
% 0.13/0.37  ipcrm: permission denied for id (822902798)
% 0.13/0.38  ipcrm: permission denied for id (822968336)
% 0.13/0.38  ipcrm: permission denied for id (823001105)
% 0.13/0.38  ipcrm: permission denied for id (823066644)
% 0.13/0.38  ipcrm: permission denied for id (823164952)
% 0.13/0.39  ipcrm: permission denied for id (823197722)
% 0.13/0.39  ipcrm: permission denied for id (823230493)
% 0.13/0.39  ipcrm: permission denied for id (823263263)
% 0.13/0.39  ipcrm: permission denied for id (823328801)
% 0.20/0.40  ipcrm: permission denied for id (823394342)
% 0.20/0.41  ipcrm: permission denied for id (823459889)
% 0.20/0.41  ipcrm: permission denied for id (823492658)
% 0.20/0.42  ipcrm: permission denied for id (823689273)
% 0.20/0.43  ipcrm: permission denied for id (823754812)
% 0.20/0.43  ipcrm: permission denied for id (823787582)
% 0.20/0.43  ipcrm: permission denied for id (823885891)
% 0.20/0.44  ipcrm: permission denied for id (823951429)
% 0.20/0.44  ipcrm: permission denied for id (823984198)
% 0.20/0.44  ipcrm: permission denied for id (824049737)
% 0.20/0.44  ipcrm: permission denied for id (824082506)
% 0.20/0.44  ipcrm: permission denied for id (824115276)
% 0.20/0.45  ipcrm: permission denied for id (824180814)
% 0.20/0.45  ipcrm: permission denied for id (824213583)
% 0.20/0.45  ipcrm: permission denied for id (824246353)
% 0.20/0.45  ipcrm: permission denied for id (824279122)
% 0.20/0.45  ipcrm: permission denied for id (824311891)
% 0.20/0.45  ipcrm: permission denied for id (824377429)
% 0.20/0.46  ipcrm: permission denied for id (824410198)
% 0.20/0.46  ipcrm: permission denied for id (824442971)
% 0.20/0.46  ipcrm: permission denied for id (824475740)
% 0.20/0.46  ipcrm: permission denied for id (824541278)
% 0.20/0.47  ipcrm: permission denied for id (824606818)
% 0.20/0.48  ipcrm: permission denied for id (824705127)
% 0.20/0.48  ipcrm: permission denied for id (824868974)
% 0.20/0.49  ipcrm: permission denied for id (824901743)
% 0.20/0.49  ipcrm: permission denied for id (824967286)
% 0.20/0.50  ipcrm: permission denied for id (825032824)
% 0.20/0.50  ipcrm: permission denied for id (825098365)
% 0.20/0.57  % (16064)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.60  % (16088)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.60  % (16079)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.78/0.62  % (16063)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.78/0.63  % (16061)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.78/0.64  % (16087)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.16/0.64  % (16072)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.16/0.65  % (16077)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.16/0.66  % (16071)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.16/0.66  % (16065)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.16/0.66  % (16062)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.40/0.67  % (16066)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.40/0.67  % (16069)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.40/0.67  % (16078)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.40/0.68  % (16070)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.40/0.68  % (16084)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.40/0.68  % (16086)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.40/0.69  % (16080)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.69  % (16090)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.40/0.69  % (16085)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.40/0.69  % (16068)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.40/0.69  % (16089)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.40/0.69  % (16067)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.40/0.69  % (16082)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.40/0.69  % (16073)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.40/0.70  % (16074)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.40/0.70  % (16076)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.40/0.70  % (16081)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.71  % (16075)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.40/0.71  % (16083)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 3.67/0.97  % (16066)Time limit reached!
% 3.67/0.97  % (16066)------------------------------
% 3.67/0.97  % (16066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.67/0.98  % (16066)Termination reason: Time limit
% 3.67/0.98  
% 3.67/0.98  % (16066)Memory used [KB]: 8955
% 3.67/0.98  % (16066)Time elapsed: 0.410 s
% 3.67/0.98  % (16066)------------------------------
% 3.67/0.98  % (16066)------------------------------
% 4.20/1.04  % (16071)Time limit reached!
% 4.20/1.04  % (16071)------------------------------
% 4.20/1.04  % (16071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.20/1.05  % (16071)Termination reason: Time limit
% 4.20/1.05  % (16071)Termination phase: Saturation
% 4.20/1.05  
% 4.20/1.05  % (16071)Memory used [KB]: 15607
% 4.20/1.05  % (16071)Time elapsed: 0.500 s
% 4.20/1.05  % (16071)------------------------------
% 4.20/1.05  % (16071)------------------------------
% 4.44/1.06  % (16073)Time limit reached!
% 4.44/1.06  % (16073)------------------------------
% 4.44/1.06  % (16073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.44/1.06  % (16073)Termination reason: Time limit
% 4.44/1.06  % (16073)Termination phase: Saturation
% 4.44/1.06  
% 4.44/1.06  % (16073)Memory used [KB]: 9083
% 4.44/1.06  % (16073)Time elapsed: 0.500 s
% 4.44/1.06  % (16073)------------------------------
% 4.44/1.06  % (16073)------------------------------
% 4.44/1.06  % (16062)Time limit reached!
% 4.44/1.06  % (16062)------------------------------
% 4.44/1.06  % (16062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.44/1.06  % (16062)Termination reason: Time limit
% 4.44/1.06  % (16062)Termination phase: Saturation
% 4.44/1.06  
% 4.44/1.06  % (16062)Memory used [KB]: 8955
% 4.44/1.06  % (16062)Time elapsed: 0.500 s
% 4.44/1.06  % (16062)------------------------------
% 4.44/1.06  % (16062)------------------------------
% 4.44/1.09  % (16078)Time limit reached!
% 4.44/1.09  % (16078)------------------------------
% 4.44/1.09  % (16078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.44/1.09  % (16078)Termination reason: Time limit
% 4.44/1.09  % (16078)Termination phase: Saturation
% 4.44/1.09  
% 4.44/1.09  % (16078)Memory used [KB]: 15095
% 4.44/1.10  % (16061)Time limit reached!
% 4.44/1.10  % (16061)------------------------------
% 4.44/1.10  % (16061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.44/1.10  % (16061)Termination reason: Time limit
% 4.44/1.10  
% 4.44/1.10  % (16061)Memory used [KB]: 4733
% 4.44/1.10  % (16061)Time elapsed: 0.520 s
% 4.44/1.10  % (16061)------------------------------
% 4.44/1.10  % (16061)------------------------------
% 4.44/1.10  % (16078)Time elapsed: 0.500 s
% 4.44/1.10  % (16078)------------------------------
% 4.44/1.10  % (16078)------------------------------
% 4.44/1.11  % (16091)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 5.07/1.15  % (16092)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 5.07/1.18  % (16094)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.40/1.18  % (16089)Time limit reached!
% 5.40/1.18  % (16089)------------------------------
% 5.40/1.18  % (16089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.40/1.18  % (16089)Termination reason: Time limit
% 5.40/1.18  % (16089)Termination phase: Saturation
% 5.40/1.18  
% 5.40/1.18  % (16089)Memory used [KB]: 9083
% 5.40/1.18  % (16089)Time elapsed: 0.600 s
% 5.40/1.18  % (16089)------------------------------
% 5.40/1.18  % (16089)------------------------------
% 5.40/1.19  % (16077)Time limit reached!
% 5.40/1.19  % (16077)------------------------------
% 5.40/1.19  % (16077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.40/1.19  % (16077)Termination reason: Time limit
% 5.40/1.19  
% 5.40/1.19  % (16077)Memory used [KB]: 17014
% 5.40/1.19  % (16077)Time elapsed: 0.633 s
% 5.40/1.19  % (16077)------------------------------
% 5.40/1.19  % (16077)------------------------------
% 5.40/1.19  % (16093)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.40/1.23  % (16095)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.40/1.23  % (16068)Time limit reached!
% 5.40/1.23  % (16068)------------------------------
% 5.40/1.23  % (16068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.40/1.23  % (16068)Termination reason: Time limit
% 5.40/1.23  % (16068)Termination phase: Saturation
% 5.40/1.23  
% 5.40/1.23  % (16068)Memory used [KB]: 10362
% 5.40/1.23  % (16068)Time elapsed: 0.600 s
% 5.40/1.23  % (16068)------------------------------
% 5.40/1.23  % (16068)------------------------------
% 5.40/1.23  % (16096)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 6.03/1.30  % (16097)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 6.36/1.31  % (16098)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.57/1.37  % (16099)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.57/1.38  % (16082)Time limit reached!
% 6.57/1.38  % (16082)------------------------------
% 6.57/1.38  % (16082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.57/1.38  % (16082)Termination reason: Time limit
% 6.57/1.38  
% 6.57/1.38  % (16082)Memory used [KB]: 4605
% 6.57/1.38  % (16082)Time elapsed: 0.825 s
% 6.57/1.38  % (16082)------------------------------
% 6.57/1.38  % (16082)------------------------------
% 7.57/1.50  % (16094)Time limit reached!
% 7.57/1.50  % (16094)------------------------------
% 7.57/1.50  % (16094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.57/1.51  % (16094)Termination reason: Time limit
% 7.57/1.51  
% 7.57/1.51  % (16094)Memory used [KB]: 8187
% 7.57/1.51  % (16094)Time elapsed: 0.408 s
% 7.57/1.51  % (16094)------------------------------
% 7.57/1.51  % (16094)------------------------------
% 7.57/1.52  % (16100)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 7.57/1.53  % (16095)Time limit reached!
% 7.57/1.53  % (16095)------------------------------
% 7.57/1.53  % (16095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.57/1.53  % (16080)Refutation found. Thanks to Tanya!
% 7.57/1.53  % SZS status Theorem for theBenchmark
% 7.57/1.53  % SZS output start Proof for theBenchmark
% 7.57/1.53  fof(f15020,plain,(
% 7.57/1.53    $false),
% 7.57/1.53    inference(avatar_sat_refutation,[],[f137,f141,f145,f149,f163,f176,f187,f193,f1232,f1264,f1285,f4278,f4504,f6025,f9454,f9496,f9629,f14046,f14125,f14469,f14612,f15019])).
% 7.57/1.53  fof(f15019,plain,(
% 7.57/1.53    ~spl8_89 | ~spl8_108),
% 7.57/1.53    inference(avatar_contradiction_clause,[],[f15018])).
% 7.57/1.53  fof(f15018,plain,(
% 7.57/1.53    $false | (~spl8_89 | ~spl8_108)),
% 7.57/1.53    inference(subsumption_resolution,[],[f14592,f15003])).
% 7.57/1.53  fof(f15003,plain,(
% 7.57/1.53    ( ! [X0] : (~r2_hidden(sK3,k4_xboole_0(X0,k4_xboole_0(X0,sK1)))) ) | ~spl8_89),
% 7.57/1.53    inference(superposition,[],[f14947,f112])).
% 7.57/1.53  fof(f112,plain,(
% 7.57/1.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.57/1.53    inference(definition_unfolding,[],[f64,f71,f71])).
% 7.57/1.53  fof(f71,plain,(
% 7.57/1.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.57/1.53    inference(cnf_transformation,[],[f12])).
% 7.57/1.53  fof(f12,axiom,(
% 7.57/1.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.57/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 7.57/1.53  fof(f64,plain,(
% 7.57/1.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.57/1.53    inference(cnf_transformation,[],[f1])).
% 7.57/1.53  fof(f1,axiom,(
% 7.57/1.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.57/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 7.57/1.53  fof(f14947,plain,(
% 7.57/1.53    ( ! [X3] : (~r2_hidden(sK3,k4_xboole_0(sK1,k4_xboole_0(sK1,X3)))) ) | ~spl8_89),
% 7.57/1.53    inference(resolution,[],[f9452,f687])).
% 7.57/1.53  fof(f687,plain,(
% 7.57/1.53    ( ! [X14,X12,X13] : (r2_hidden(X14,k5_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),k4_xboole_0(X12,X13))) | ~r2_hidden(X14,k4_xboole_0(X12,k4_xboole_0(X12,X13)))) )),
% 7.57/1.53    inference(superposition,[],[f157,f115])).
% 7.57/1.53  fof(f115,plain,(
% 7.57/1.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.57/1.53    inference(definition_unfolding,[],[f70,f71])).
% 7.57/1.53  fof(f70,plain,(
% 7.57/1.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.57/1.53    inference(cnf_transformation,[],[f11])).
% 7.57/1.53  fof(f11,axiom,(
% 7.57/1.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.57/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 7.57/1.53  fof(f157,plain,(
% 7.57/1.53    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0))) | ~r2_hidden(X4,X0)) )),
% 7.57/1.53    inference(forward_demodulation,[],[f132,f113])).
% 7.57/1.53  fof(f113,plain,(
% 7.57/1.53    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.57/1.53    inference(definition_unfolding,[],[f67,f105])).
% 7.57/1.53  fof(f105,plain,(
% 7.57/1.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.57/1.53    inference(definition_unfolding,[],[f66,f104])).
% 7.57/1.53  fof(f104,plain,(
% 7.57/1.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.57/1.53    inference(definition_unfolding,[],[f65,f103])).
% 7.57/1.53  fof(f103,plain,(
% 7.57/1.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.57/1.53    inference(definition_unfolding,[],[f86,f102])).
% 7.57/1.53  fof(f102,plain,(
% 7.57/1.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.57/1.53    inference(definition_unfolding,[],[f96,f101])).
% 7.57/1.53  fof(f101,plain,(
% 7.57/1.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.57/1.53    inference(definition_unfolding,[],[f97,f100])).
% 7.57/1.53  fof(f100,plain,(
% 7.57/1.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.57/1.53    inference(definition_unfolding,[],[f98,f99])).
% 7.57/1.53  fof(f99,plain,(
% 7.57/1.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.57/1.53    inference(cnf_transformation,[],[f23])).
% 7.57/1.53  fof(f23,axiom,(
% 7.57/1.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 7.57/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 7.57/1.53  fof(f98,plain,(
% 7.57/1.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.57/1.53    inference(cnf_transformation,[],[f22])).
% 7.57/1.53  fof(f22,axiom,(
% 7.57/1.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.57/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 7.57/1.53  fof(f97,plain,(
% 7.57/1.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.57/1.53    inference(cnf_transformation,[],[f21])).
% 7.57/1.53  fof(f21,axiom,(
% 7.57/1.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 7.57/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 7.57/1.53  fof(f96,plain,(
% 7.57/1.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.57/1.53    inference(cnf_transformation,[],[f20])).
% 7.57/1.53  fof(f20,axiom,(
% 7.57/1.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 7.57/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 7.57/1.53  fof(f86,plain,(
% 7.57/1.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.57/1.53    inference(cnf_transformation,[],[f19])).
% 7.57/1.53  fof(f19,axiom,(
% 7.57/1.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 7.57/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 7.57/1.53  fof(f65,plain,(
% 7.57/1.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.57/1.53    inference(cnf_transformation,[],[f18])).
% 7.57/1.53  fof(f18,axiom,(
% 7.57/1.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.57/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 7.57/1.53  fof(f66,plain,(
% 7.57/1.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.57/1.53    inference(cnf_transformation,[],[f25])).
% 7.57/1.53  fof(f25,axiom,(
% 7.57/1.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.57/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 7.57/1.53  fof(f67,plain,(
% 7.57/1.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.57/1.53    inference(cnf_transformation,[],[f15])).
% 7.57/1.53  fof(f15,axiom,(
% 7.57/1.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.57/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 7.57/1.53  fof(f132,plain,(
% 7.57/1.53    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 7.57/1.53    inference(equality_resolution,[],[f126])).
% 7.57/1.53  fof(f126,plain,(
% 7.57/1.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 7.57/1.53    inference(definition_unfolding,[],[f88,f105])).
% 7.57/1.53  fof(f88,plain,(
% 7.57/1.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 7.57/1.53    inference(cnf_transformation,[],[f53])).
% 7.57/1.53  fof(f53,plain,(
% 7.57/1.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK7(X0,X1,X2),X1) & ~r2_hidden(sK7(X0,X1,X2),X0)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.57/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f51,f52])).
% 7.57/1.53  fof(f52,plain,(
% 7.57/1.53    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK7(X0,X1,X2),X1) & ~r2_hidden(sK7(X0,X1,X2),X0)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 7.57/1.53    introduced(choice_axiom,[])).
% 7.57/1.53  fof(f51,plain,(
% 7.57/1.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.57/1.53    inference(rectify,[],[f50])).
% 7.57/1.53  fof(f50,plain,(
% 7.57/1.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.57/1.53    inference(flattening,[],[f49])).
% 7.57/1.53  fof(f49,plain,(
% 7.57/1.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.57/1.53    inference(nnf_transformation,[],[f3])).
% 7.57/1.53  fof(f3,axiom,(
% 7.57/1.53    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 7.57/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 7.57/1.53  fof(f9452,plain,(
% 7.57/1.53    ( ! [X5] : (~r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X5)),k4_xboole_0(sK1,X5)))) ) | ~spl8_89),
% 7.57/1.53    inference(avatar_component_clause,[],[f9451])).
% 7.57/1.53  fof(f9451,plain,(
% 7.57/1.53    spl8_89 <=> ! [X5] : ~r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X5)),k4_xboole_0(sK1,X5)))),
% 7.57/1.53    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).
% 7.57/1.53  fof(f14592,plain,(
% 7.57/1.53    r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl8_108),
% 7.57/1.53    inference(avatar_component_clause,[],[f14591])).
% 7.57/1.53  fof(f14591,plain,(
% 7.57/1.53    spl8_108 <=> r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 7.57/1.53    introduced(avatar_definition,[new_symbols(naming,[spl8_108])])).
% 7.57/1.53  fof(f14612,plain,(
% 7.57/1.53    spl8_108 | ~spl8_100),
% 7.57/1.53    inference(avatar_split_clause,[],[f14611,f14121,f14591])).
% 7.57/1.53  fof(f14121,plain,(
% 7.57/1.53    spl8_100 <=> ! [X0] : r2_hidden(sK3,k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0)))),
% 7.57/1.53    introduced(avatar_definition,[new_symbols(naming,[spl8_100])])).
% 7.57/1.53  fof(f14611,plain,(
% 7.57/1.53    r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl8_100),
% 7.57/1.53    inference(forward_demodulation,[],[f14587,f61])).
% 7.57/1.53  fof(f61,plain,(
% 7.57/1.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.57/1.53    inference(cnf_transformation,[],[f10])).
% 7.57/1.53  fof(f10,axiom,(
% 7.57/1.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.57/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 7.57/1.53  fof(f14587,plain,(
% 7.57/1.53    r2_hidden(sK3,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_xboole_0)) | ~spl8_100),
% 7.57/1.53    inference(superposition,[],[f14122,f5041])).
% 7.57/1.53  fof(f5041,plain,(
% 7.57/1.53    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 7.57/1.53    inference(forward_demodulation,[],[f5039,f61])).
% 7.57/1.53  fof(f5039,plain,(
% 7.57/1.53    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)) = X1) )),
% 7.57/1.53    inference(superposition,[],[f2680,f113])).
% 7.57/1.53  fof(f2680,plain,(
% 7.57/1.53    ( ! [X1] : (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1) )),
% 7.57/1.53    inference(forward_demodulation,[],[f2664,f61])).
% 7.57/1.53  fof(f2664,plain,(
% 7.57/1.53    ( ! [X1] : (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(X1,k1_xboole_0))) = X1) )),
% 7.57/1.53    inference(superposition,[],[f152,f110])).
% 7.57/1.53  fof(f110,plain,(
% 7.57/1.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 7.57/1.53    inference(definition_unfolding,[],[f60,f71])).
% 7.57/1.53  fof(f60,plain,(
% 7.57/1.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 7.57/1.53    inference(cnf_transformation,[],[f8])).
% 7.57/1.53  fof(f8,axiom,(
% 7.57/1.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 7.57/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 7.57/1.53  fof(f152,plain,(
% 7.57/1.53    ( ! [X0,X1] : (k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0) )),
% 7.57/1.53    inference(forward_demodulation,[],[f116,f111])).
% 7.57/1.53  fof(f111,plain,(
% 7.57/1.53    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 7.57/1.53    inference(definition_unfolding,[],[f63,f104,f104])).
% 7.57/1.53  fof(f63,plain,(
% 7.57/1.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.57/1.53    inference(cnf_transformation,[],[f16])).
% 7.57/1.53  fof(f16,axiom,(
% 7.57/1.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.57/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 7.57/1.53  fof(f116,plain,(
% 7.57/1.53    ( ! [X0,X1] : (k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0) )),
% 7.57/1.53    inference(definition_unfolding,[],[f72,f105,f71])).
% 7.57/1.53  fof(f72,plain,(
% 7.57/1.53    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 7.57/1.53    inference(cnf_transformation,[],[f13])).
% 7.57/1.53  fof(f13,axiom,(
% 7.57/1.53    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 7.57/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 7.57/1.53  fof(f14122,plain,(
% 7.57/1.53    ( ! [X0] : (r2_hidden(sK3,k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0)))) ) | ~spl8_100),
% 7.57/1.53    inference(avatar_component_clause,[],[f14121])).
% 7.57/1.53  fof(f14469,plain,(
% 7.57/1.53    ~spl8_66 | ~spl8_88 | ~spl8_94),
% 7.57/1.53    inference(avatar_split_clause,[],[f14465,f14044,f6023,f4497])).
% 7.57/1.53  fof(f4497,plain,(
% 7.57/1.53    spl8_66 <=> r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),sK1)),
% 7.57/1.53    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).
% 7.57/1.53  fof(f6023,plain,(
% 7.57/1.53    spl8_88 <=> r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),sK0)),
% 7.57/1.53    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).
% 7.57/1.53  fof(f14044,plain,(
% 7.57/1.53    spl8_94 <=> ! [X23] : (~r2_hidden(X23,sK1) | ~r2_hidden(X23,sK0))),
% 7.57/1.53    introduced(avatar_definition,[new_symbols(naming,[spl8_94])])).
% 7.57/1.53  fof(f14465,plain,(
% 7.57/1.53    ~r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),sK1) | (~spl8_88 | ~spl8_94)),
% 7.57/1.53    inference(resolution,[],[f14045,f6024])).
% 7.57/1.53  fof(f6024,plain,(
% 7.57/1.53    r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),sK0) | ~spl8_88),
% 7.57/1.53    inference(avatar_component_clause,[],[f6023])).
% 7.57/1.53  fof(f14045,plain,(
% 7.57/1.53    ( ! [X23] : (~r2_hidden(X23,sK0) | ~r2_hidden(X23,sK1)) ) | ~spl8_94),
% 7.57/1.53    inference(avatar_component_clause,[],[f14044])).
% 7.57/1.53  fof(f14125,plain,(
% 7.57/1.53    spl8_94 | spl8_100 | ~spl8_92),
% 7.57/1.53    inference(avatar_split_clause,[],[f14098,f14036,f14121,f14044])).
% 7.57/1.53  fof(f14036,plain,(
% 7.57/1.53    spl8_92 <=> ! [X19] : (r2_hidden(sK3,X19) | ~r2_hidden(sK4(sK0,sK1),X19))),
% 7.57/1.53    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).
% 7.57/1.53  fof(f14098,plain,(
% 7.57/1.53    ( ! [X4,X3] : (r2_hidden(sK3,k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X3))) | ~r2_hidden(X4,sK1) | ~r2_hidden(X4,sK0)) ) | ~spl8_92),
% 7.57/1.53    inference(resolution,[],[f14061,f937])).
% 7.57/1.53  fof(f937,plain,(
% 7.57/1.53    ( ! [X6,X7,X5] : (r2_hidden(sK4(X5,X6),k4_xboole_0(X5,k4_xboole_0(X5,X6))) | ~r2_hidden(X7,X6) | ~r2_hidden(X7,X5)) )),
% 7.57/1.53    inference(resolution,[],[f118,f77])).
% 7.57/1.53  fof(f77,plain,(
% 7.57/1.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.57/1.53    inference(cnf_transformation,[],[f42])).
% 7.57/1.53  fof(f42,plain,(
% 7.57/1.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.57/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f41])).
% 7.57/1.53  fof(f41,plain,(
% 7.57/1.53    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 7.57/1.53    introduced(choice_axiom,[])).
% 7.57/1.54  fof(f34,plain,(
% 7.57/1.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.57/1.54    inference(ennf_transformation,[],[f30])).
% 7.57/1.54  fof(f30,plain,(
% 7.57/1.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.57/1.54    inference(rectify,[],[f5])).
% 7.57/1.54  fof(f5,axiom,(
% 7.57/1.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 7.57/1.54  fof(f118,plain,(
% 7.57/1.54    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.57/1.54    inference(definition_unfolding,[],[f73,f71])).
% 7.57/1.54  fof(f73,plain,(
% 7.57/1.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 7.57/1.54    inference(cnf_transformation,[],[f40])).
% 7.57/1.54  fof(f40,plain,(
% 7.57/1.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.57/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f39])).
% 7.57/1.54  fof(f39,plain,(
% 7.57/1.54    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 7.57/1.54    introduced(choice_axiom,[])).
% 7.57/1.54  fof(f33,plain,(
% 7.57/1.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.57/1.54    inference(ennf_transformation,[],[f29])).
% 7.57/1.54  fof(f29,plain,(
% 7.57/1.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.57/1.54    inference(rectify,[],[f6])).
% 7.57/1.54  fof(f6,axiom,(
% 7.57/1.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 7.57/1.54  fof(f14061,plain,(
% 7.57/1.54    ( ! [X12,X11] : (~r2_hidden(sK4(sK0,sK1),X11) | r2_hidden(sK3,k5_xboole_0(X12,k4_xboole_0(X11,X12)))) ) | ~spl8_92),
% 7.57/1.54    inference(resolution,[],[f14037,f156])).
% 7.57/1.54  fof(f156,plain,(
% 7.57/1.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 7.57/1.54    inference(forward_demodulation,[],[f131,f113])).
% 7.57/1.54  fof(f131,plain,(
% 7.57/1.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 7.57/1.54    inference(equality_resolution,[],[f125])).
% 7.57/1.54  fof(f125,plain,(
% 7.57/1.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 7.57/1.54    inference(definition_unfolding,[],[f89,f105])).
% 7.57/1.54  fof(f89,plain,(
% 7.57/1.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 7.57/1.54    inference(cnf_transformation,[],[f53])).
% 7.57/1.54  fof(f14037,plain,(
% 7.57/1.54    ( ! [X19] : (r2_hidden(sK3,X19) | ~r2_hidden(sK4(sK0,sK1),X19)) ) | ~spl8_92),
% 7.57/1.54    inference(avatar_component_clause,[],[f14036])).
% 7.57/1.54  fof(f14046,plain,(
% 7.57/1.54    spl8_94 | spl8_92 | ~spl8_4),
% 7.57/1.54    inference(avatar_split_clause,[],[f14026,f147,f14036,f14044])).
% 7.57/1.54  fof(f147,plain,(
% 7.57/1.54    spl8_4 <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),
% 7.57/1.54    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 7.57/1.54  fof(f14026,plain,(
% 7.57/1.54    ( ! [X23,X22] : (r2_hidden(sK3,X22) | ~r2_hidden(sK4(sK0,sK1),X22) | ~r2_hidden(X23,sK1) | ~r2_hidden(X23,sK0)) ) | ~spl8_4),
% 7.57/1.54    inference(resolution,[],[f13992,f937])).
% 7.57/1.54  fof(f13992,plain,(
% 7.57/1.54    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | r2_hidden(sK3,X1) | ~r2_hidden(X0,X1)) ) | ~spl8_4),
% 7.57/1.54    inference(resolution,[],[f1327,f196])).
% 7.57/1.54  fof(f196,plain,(
% 7.57/1.54    ( ! [X0] : (r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | ~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | ~spl8_4),
% 7.57/1.54    inference(resolution,[],[f79,f148])).
% 7.57/1.54  fof(f148,plain,(
% 7.57/1.54    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | ~spl8_4),
% 7.57/1.54    inference(avatar_component_clause,[],[f147])).
% 7.57/1.54  fof(f79,plain,(
% 7.57/1.54    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 7.57/1.54    inference(cnf_transformation,[],[f46])).
% 7.57/1.54  fof(f46,plain,(
% 7.57/1.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.57/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).
% 7.57/1.54  fof(f45,plain,(
% 7.57/1.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 7.57/1.54    introduced(choice_axiom,[])).
% 7.57/1.54  fof(f44,plain,(
% 7.57/1.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.57/1.54    inference(rectify,[],[f43])).
% 7.57/1.54  fof(f43,plain,(
% 7.57/1.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.57/1.54    inference(nnf_transformation,[],[f36])).
% 7.57/1.54  fof(f36,plain,(
% 7.57/1.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.57/1.54    inference(ennf_transformation,[],[f2])).
% 7.57/1.54  fof(f2,axiom,(
% 7.57/1.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 7.57/1.54  fof(f1327,plain,(
% 7.57/1.54    ( ! [X6,X7,X5] : (~r2_hidden(X7,k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5)) | ~r2_hidden(X7,X6) | r2_hidden(X5,X6)) )),
% 7.57/1.54    inference(resolution,[],[f119,f77])).
% 7.57/1.54  fof(f119,plain,(
% 7.57/1.54    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 7.57/1.54    inference(definition_unfolding,[],[f78,f106])).
% 7.57/1.54  fof(f106,plain,(
% 7.57/1.54    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.57/1.54    inference(definition_unfolding,[],[f62,f104])).
% 7.57/1.54  fof(f62,plain,(
% 7.57/1.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.57/1.54    inference(cnf_transformation,[],[f17])).
% 7.57/1.54  fof(f17,axiom,(
% 7.57/1.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 7.57/1.54  fof(f78,plain,(
% 7.57/1.54    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 7.57/1.54    inference(cnf_transformation,[],[f35])).
% 7.57/1.54  fof(f35,plain,(
% 7.57/1.54    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 7.57/1.54    inference(ennf_transformation,[],[f24])).
% 7.57/1.54  fof(f24,axiom,(
% 7.57/1.54    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 7.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 7.57/1.54  fof(f9629,plain,(
% 7.57/1.54    ~spl8_58 | spl8_31),
% 7.57/1.54    inference(avatar_split_clause,[],[f9628,f1227,f3519])).
% 7.57/1.54  fof(f3519,plain,(
% 7.57/1.54    spl8_58 <=> r2_hidden(sK3,sK1)),
% 7.57/1.54    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).
% 7.57/1.54  fof(f1227,plain,(
% 7.57/1.54    spl8_31 <=> r2_hidden(sK3,k5_xboole_0(k1_xboole_0,sK1))),
% 7.57/1.54    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 7.57/1.54  fof(f9628,plain,(
% 7.57/1.54    ~r2_hidden(sK3,sK1) | spl8_31),
% 7.57/1.54    inference(forward_demodulation,[],[f1228,f5041])).
% 7.57/1.54  fof(f1228,plain,(
% 7.57/1.54    ~r2_hidden(sK3,k5_xboole_0(k1_xboole_0,sK1)) | spl8_31),
% 7.57/1.54    inference(avatar_component_clause,[],[f1227])).
% 7.57/1.54  fof(f9496,plain,(
% 7.57/1.54    ~spl8_2 | ~spl8_9 | ~spl8_34),
% 7.57/1.54    inference(avatar_contradiction_clause,[],[f9494])).
% 7.57/1.54  fof(f9494,plain,(
% 7.57/1.54    $false | (~spl8_2 | ~spl8_9 | ~spl8_34)),
% 7.57/1.54    inference(resolution,[],[f1260,f203])).
% 7.57/1.54  fof(f203,plain,(
% 7.57/1.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl8_2 | ~spl8_9)),
% 7.57/1.54    inference(forward_demodulation,[],[f202,f164])).
% 7.57/1.54  fof(f164,plain,(
% 7.57/1.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 7.57/1.54    inference(superposition,[],[f110,f61])).
% 7.57/1.54  fof(f202,plain,(
% 7.57/1.54    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK1,sK1))) ) | (~spl8_2 | ~spl8_9)),
% 7.57/1.54    inference(forward_demodulation,[],[f201,f192])).
% 7.57/1.54  fof(f192,plain,(
% 7.57/1.54    sK1 = k4_xboole_0(sK1,sK2) | ~spl8_9),
% 7.57/1.54    inference(avatar_component_clause,[],[f191])).
% 7.57/1.54  fof(f191,plain,(
% 7.57/1.54    spl8_9 <=> sK1 = k4_xboole_0(sK1,sK2)),
% 7.57/1.54    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 7.57/1.54  fof(f201,plain,(
% 7.57/1.54    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ) | ~spl8_2),
% 7.57/1.54    inference(forward_demodulation,[],[f198,f112])).
% 7.57/1.54  fof(f198,plain,(
% 7.57/1.54    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))) ) | ~spl8_2),
% 7.57/1.54    inference(resolution,[],[f117,f140])).
% 7.57/1.54  fof(f140,plain,(
% 7.57/1.54    r1_xboole_0(sK2,sK1) | ~spl8_2),
% 7.57/1.54    inference(avatar_component_clause,[],[f139])).
% 7.57/1.54  fof(f139,plain,(
% 7.57/1.54    spl8_2 <=> r1_xboole_0(sK2,sK1)),
% 7.57/1.54    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 7.57/1.54  fof(f117,plain,(
% 7.57/1.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.57/1.54    inference(definition_unfolding,[],[f74,f71])).
% 7.57/1.54  % (16095)Termination reason: Time limit
% 7.57/1.54  fof(f74,plain,(
% 7.57/1.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.57/1.54    inference(cnf_transformation,[],[f40])).
% 7.57/1.54  fof(f1260,plain,(
% 7.57/1.54    r2_hidden(sK3,k1_xboole_0) | ~spl8_34),
% 7.57/1.54    inference(avatar_component_clause,[],[f1259])).
% 7.57/1.54  fof(f1259,plain,(
% 7.57/1.54    spl8_34 <=> r2_hidden(sK3,k1_xboole_0)),
% 7.57/1.54    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 7.57/1.54  fof(f9454,plain,(
% 7.57/1.54    spl8_89 | spl8_58 | spl8_37),
% 7.57/1.54    inference(avatar_split_clause,[],[f9449,f1283,f3519,f9451])).
% 7.57/1.54  fof(f1283,plain,(
% 7.57/1.54    spl8_37 <=> r2_hidden(sK3,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))))),
% 7.57/1.54    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 7.57/1.54  fof(f9449,plain,(
% 7.57/1.54    ( ! [X5] : (r2_hidden(sK3,sK1) | ~r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X5)),k4_xboole_0(sK1,X5)))) ) | spl8_37),
% 7.57/1.54    inference(forward_demodulation,[],[f9448,f8586])).
% 7.57/1.54  fof(f8586,plain,(
% 7.57/1.54    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2) )),
% 7.57/1.54    inference(superposition,[],[f2677,f151])).
% 7.57/1.54  fof(f151,plain,(
% 7.57/1.54    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0))) )),
% 7.57/1.54    inference(forward_demodulation,[],[f150,f113])).
% 7.57/1.54  fof(f150,plain,(
% 7.57/1.54    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0))) )),
% 7.57/1.54    inference(forward_demodulation,[],[f114,f113])).
% 7.57/1.54  fof(f114,plain,(
% 7.57/1.54    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,X0)))) )),
% 7.57/1.54    inference(definition_unfolding,[],[f68,f105,f105])).
% 7.57/1.54  fof(f68,plain,(
% 7.57/1.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.57/1.54    inference(cnf_transformation,[],[f9])).
% 7.57/1.54  fof(f9,axiom,(
% 7.57/1.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 7.57/1.54  fof(f2677,plain,(
% 7.57/1.54    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X2,X3))) = X2) )),
% 7.57/1.54    inference(superposition,[],[f152,f113])).
% 7.57/1.54  fof(f9448,plain,(
% 7.57/1.54    ( ! [X5] : (r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X5)),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X5))))) | ~r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X5)),k4_xboole_0(sK1,X5)))) ) | spl8_37),
% 7.57/1.54    inference(forward_demodulation,[],[f9425,f112])).
% 7.57/1.54  fof(f9425,plain,(
% 7.57/1.54    ( ! [X5] : (r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X5)),k4_xboole_0(k4_xboole_0(sK1,X5),k4_xboole_0(k4_xboole_0(sK1,X5),sK1)))) | ~r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X5)),k4_xboole_0(sK1,X5)))) ) | spl8_37),
% 7.57/1.54    inference(resolution,[],[f479,f8035])).
% 7.57/1.54  fof(f8035,plain,(
% 7.57/1.54    ( ! [X0] : (r2_hidden(sK3,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) | ~r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,X0)))) ) | spl8_37),
% 7.57/1.54    inference(superposition,[],[f8020,f112])).
% 7.57/1.54  fof(f8020,plain,(
% 7.57/1.54    ( ! [X0] : (r2_hidden(sK3,k4_xboole_0(X0,k4_xboole_0(X0,sK1))) | ~r2_hidden(sK3,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),k4_xboole_0(sK1,X0)))) ) | spl8_37),
% 7.57/1.54    inference(forward_demodulation,[],[f8019,f115])).
% 7.57/1.54  fof(f8019,plain,(
% 7.57/1.54    ( ! [X0] : (~r2_hidden(sK3,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))))) | r2_hidden(sK3,k4_xboole_0(X0,k4_xboole_0(X0,sK1)))) ) | spl8_37),
% 7.57/1.54    inference(forward_demodulation,[],[f8003,f112])).
% 7.57/1.54  fof(f8003,plain,(
% 7.57/1.54    ( ! [X0] : (r2_hidden(sK3,k4_xboole_0(X0,k4_xboole_0(X0,sK1))) | ~r2_hidden(sK3,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),k4_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(k4_xboole_0(sK1,X0),sK1))))) ) | spl8_37),
% 7.57/1.54    inference(superposition,[],[f7557,f112])).
% 7.57/1.54  fof(f7557,plain,(
% 7.57/1.54    ( ! [X211] : (r2_hidden(sK3,k4_xboole_0(sK1,X211)) | ~r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,X211),k4_xboole_0(X211,k4_xboole_0(X211,sK1))))) ) | spl8_37),
% 7.57/1.54    inference(forward_demodulation,[],[f7556,f5041])).
% 7.57/1.54  fof(f7556,plain,(
% 7.57/1.54    ( ! [X211] : (r2_hidden(sK3,k4_xboole_0(k5_xboole_0(k1_xboole_0,sK1),X211)) | ~r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,X211),k4_xboole_0(X211,k4_xboole_0(X211,sK1))))) ) | spl8_37),
% 7.57/1.54    inference(forward_demodulation,[],[f7555,f5041])).
% 7.57/1.54  fof(f7555,plain,(
% 7.57/1.54    ( ! [X211] : (r2_hidden(sK3,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1)),X211)) | ~r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,X211),k4_xboole_0(X211,k4_xboole_0(X211,sK1))))) ) | spl8_37),
% 7.57/1.54    inference(forward_demodulation,[],[f7554,f5041])).
% 7.57/1.54  fof(f7554,plain,(
% 7.57/1.54    ( ! [X211] : (r2_hidden(sK3,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))),X211)) | ~r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,X211),k4_xboole_0(X211,k4_xboole_0(X211,sK1))))) ) | spl8_37),
% 7.57/1.54    inference(forward_demodulation,[],[f7553,f681])).
% 7.57/1.54  fof(f681,plain,(
% 7.57/1.54    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) )),
% 7.57/1.54    inference(superposition,[],[f115,f112])).
% 7.57/1.54  fof(f7553,plain,(
% 7.57/1.54    ( ! [X211] : (~r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,X211),k4_xboole_0(X211,k4_xboole_0(X211,sK1)))) | r2_hidden(sK3,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))),k4_xboole_0(X211,k4_xboole_0(X211,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1)))))))) ) | spl8_37),
% 7.57/1.54    inference(forward_demodulation,[],[f7552,f681])).
% 7.57/1.54  fof(f7552,plain,(
% 7.57/1.54    ( ! [X211] : (~r2_hidden(sK3,k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X211,k4_xboole_0(X211,sK1))),k4_xboole_0(X211,k4_xboole_0(X211,sK1)))) | r2_hidden(sK3,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))),k4_xboole_0(X211,k4_xboole_0(X211,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1)))))))) ) | spl8_37),
% 7.57/1.54    inference(forward_demodulation,[],[f7551,f5041])).
% 7.57/1.54  fof(f7551,plain,(
% 7.57/1.54    ( ! [X211] : (~r2_hidden(sK3,k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k4_xboole_0(X211,k4_xboole_0(X211,k5_xboole_0(k1_xboole_0,sK1)))),k4_xboole_0(X211,k4_xboole_0(X211,k5_xboole_0(k1_xboole_0,sK1))))) | r2_hidden(sK3,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))),k4_xboole_0(X211,k4_xboole_0(X211,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1)))))))) ) | spl8_37),
% 7.57/1.54    inference(forward_demodulation,[],[f7550,f5041])).
% 7.57/1.54  
% 7.57/1.54  % (16095)Memory used [KB]: 13432
% 7.57/1.54  % (16095)Time elapsed: 0.409 s
% 7.57/1.54  % (16095)------------------------------
% 7.57/1.54  % (16095)------------------------------
% 7.57/1.54  fof(f7550,plain,(
% 7.57/1.54    ( ! [X211] : (~r2_hidden(sK3,k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1)),k4_xboole_0(X211,k4_xboole_0(X211,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))))),k4_xboole_0(X211,k4_xboole_0(X211,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1)))))) | r2_hidden(sK3,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))),k4_xboole_0(X211,k4_xboole_0(X211,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1)))))))) ) | spl8_37),
% 7.57/1.54    inference(forward_demodulation,[],[f7148,f5041])).
% 7.57/1.54  fof(f7148,plain,(
% 7.57/1.54    ( ! [X211] : (~r2_hidden(sK3,k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))),k4_xboole_0(X211,k4_xboole_0(X211,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1)))))),k4_xboole_0(X211,k4_xboole_0(X211,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))))))) | r2_hidden(sK3,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))),k4_xboole_0(X211,k4_xboole_0(X211,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1)))))))) ) | spl8_37),
% 7.57/1.54    inference(superposition,[],[f1289,f674])).
% 7.57/1.54  fof(f674,plain,(
% 7.57/1.54    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))) )),
% 7.57/1.54    inference(superposition,[],[f115,f112])).
% 7.57/1.54  fof(f1289,plain,(
% 7.57/1.54    ( ! [X0] : (~r2_hidden(sK3,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))),X0))) | r2_hidden(sK3,X0)) ) | spl8_37),
% 7.57/1.54    inference(resolution,[],[f1284,f158])).
% 7.57/1.54  fof(f158,plain,(
% 7.57/1.54    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0))) | r2_hidden(X4,X0)) )),
% 7.57/1.54    inference(forward_demodulation,[],[f133,f113])).
% 7.57/1.54  fof(f133,plain,(
% 7.57/1.54    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.57/1.54    inference(equality_resolution,[],[f127])).
% 7.57/1.54  fof(f127,plain,(
% 7.57/1.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 7.57/1.54    inference(definition_unfolding,[],[f87,f105])).
% 7.57/1.54  fof(f87,plain,(
% 7.57/1.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 7.57/1.54    inference(cnf_transformation,[],[f53])).
% 7.57/1.54  fof(f1284,plain,(
% 7.57/1.54    ~r2_hidden(sK3,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1)))) | spl8_37),
% 7.57/1.54    inference(avatar_component_clause,[],[f1283])).
% 7.57/1.54  fof(f479,plain,(
% 7.57/1.54    ( ! [X6,X7,X5] : (~r2_hidden(X7,k4_xboole_0(X5,X6)) | r2_hidden(X7,k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,k4_xboole_0(X6,X5))))) )),
% 7.57/1.54    inference(superposition,[],[f157,f112])).
% 7.57/1.54  fof(f6025,plain,(
% 7.57/1.54    spl8_7 | spl8_88 | ~spl8_2 | ~spl8_62),
% 7.57/1.54    inference(avatar_split_clause,[],[f6008,f4271,f139,f6023,f174])).
% 7.57/1.54  fof(f174,plain,(
% 7.57/1.54    spl8_7 <=> k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1)),
% 7.57/1.54    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 7.57/1.54  fof(f4271,plain,(
% 7.57/1.54    spl8_62 <=> r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)))),
% 7.57/1.54    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).
% 7.57/1.54  fof(f6008,plain,(
% 7.57/1.54    r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),sK0) | k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1) | (~spl8_2 | ~spl8_62)),
% 7.57/1.54    inference(resolution,[],[f1943,f4272])).
% 7.57/1.54  fof(f4272,plain,(
% 7.57/1.54    r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),k5_xboole_0(sK0,k4_xboole_0(sK2,sK0))) | ~spl8_62),
% 7.57/1.54    inference(avatar_component_clause,[],[f4271])).
% 7.57/1.54  fof(f1943,plain,(
% 7.57/1.54    ( ! [X10,X9] : (~r2_hidden(sK5(X9,sK1),k5_xboole_0(X10,k4_xboole_0(sK2,X10))) | r2_hidden(sK5(X9,sK1),X10) | k4_xboole_0(X9,sK1) = X9) ) | ~spl8_2),
% 7.57/1.54    inference(resolution,[],[f1202,f82])).
% 7.57/1.54  fof(f82,plain,(
% 7.57/1.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 7.57/1.54    inference(cnf_transformation,[],[f47])).
% 7.57/1.54  fof(f47,plain,(
% 7.57/1.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 7.57/1.54    inference(nnf_transformation,[],[f14])).
% 7.57/1.54  fof(f14,axiom,(
% 7.57/1.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 7.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 7.57/1.54  fof(f1202,plain,(
% 7.57/1.54    ( ! [X19,X20] : (r1_xboole_0(X19,sK1) | r2_hidden(sK5(X19,sK1),X20) | ~r2_hidden(sK5(X19,sK1),k5_xboole_0(X20,k4_xboole_0(sK2,X20)))) ) | ~spl8_2),
% 7.57/1.54    inference(resolution,[],[f158,f180])).
% 7.57/1.54  fof(f180,plain,(
% 7.57/1.54    ( ! [X1] : (~r2_hidden(sK5(X1,sK1),sK2) | r1_xboole_0(X1,sK1)) ) | ~spl8_2),
% 7.57/1.54    inference(resolution,[],[f177,f76])).
% 7.57/1.54  fof(f76,plain,(
% 7.57/1.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 7.57/1.54    inference(cnf_transformation,[],[f42])).
% 7.57/1.54  fof(f177,plain,(
% 7.57/1.54    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK2)) ) | ~spl8_2),
% 7.57/1.54    inference(resolution,[],[f77,f140])).
% 7.57/1.54  fof(f4504,plain,(
% 7.57/1.54    spl8_66 | spl8_5),
% 7.57/1.54    inference(avatar_split_clause,[],[f4503,f161,f4497])).
% 7.57/1.54  fof(f161,plain,(
% 7.57/1.54    spl8_5 <=> r1_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1)),
% 7.57/1.54    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 7.57/1.54  fof(f4503,plain,(
% 7.57/1.54    r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),sK1) | spl8_5),
% 7.57/1.54    inference(forward_demodulation,[],[f4502,f61])).
% 7.57/1.54  fof(f4502,plain,(
% 7.57/1.54    r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),k4_xboole_0(sK1,k1_xboole_0)) | spl8_5),
% 7.57/1.54    inference(forward_demodulation,[],[f4485,f164])).
% 7.57/1.54  fof(f4485,plain,(
% 7.57/1.54    r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) | spl8_5),
% 7.57/1.54    inference(superposition,[],[f4471,f685])).
% 7.57/1.54  fof(f685,plain,(
% 7.57/1.54    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) )),
% 7.57/1.54    inference(superposition,[],[f107,f115])).
% 7.57/1.54  fof(f107,plain,(
% 7.57/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.57/1.54    inference(definition_unfolding,[],[f69,f71])).
% 7.57/1.54  fof(f69,plain,(
% 7.57/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.57/1.54    inference(cnf_transformation,[],[f7])).
% 7.57/1.54  fof(f7,axiom,(
% 7.57/1.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 7.57/1.54  fof(f4471,plain,(
% 7.57/1.54    ( ! [X0] : (r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),k5_xboole_0(X0,k4_xboole_0(sK1,X0)))) ) | spl8_5),
% 7.57/1.54    inference(resolution,[],[f257,f162])).
% 7.57/1.54  fof(f162,plain,(
% 7.57/1.54    ~r1_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1) | spl8_5),
% 7.57/1.54    inference(avatar_component_clause,[],[f161])).
% 7.57/1.54  fof(f257,plain,(
% 7.57/1.54    ( ! [X6,X8,X7] : (r1_xboole_0(X6,X7) | r2_hidden(sK5(X6,X7),k5_xboole_0(X8,k4_xboole_0(X7,X8)))) )),
% 7.57/1.54    inference(resolution,[],[f156,f76])).
% 7.57/1.54  fof(f4278,plain,(
% 7.57/1.54    spl8_62 | spl8_5),
% 7.57/1.54    inference(avatar_split_clause,[],[f4277,f161,f4271])).
% 7.57/1.54  fof(f4277,plain,(
% 7.57/1.54    r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),k5_xboole_0(sK0,k4_xboole_0(sK2,sK0))) | spl8_5),
% 7.57/1.54    inference(forward_demodulation,[],[f4276,f61])).
% 7.57/1.54  fof(f4276,plain,(
% 7.57/1.54    r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),k1_xboole_0)) | spl8_5),
% 7.57/1.54    inference(forward_demodulation,[],[f4263,f164])).
% 7.57/1.54  fof(f4263,plain,(
% 7.57/1.54    r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK2,sK0))))) | spl8_5),
% 7.57/1.54    inference(superposition,[],[f4242,f685])).
% 7.57/1.54  fof(f4242,plain,(
% 7.57/1.54    ( ! [X0] : (r2_hidden(sK5(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1),k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),X0)))) ) | spl8_5),
% 7.57/1.54    inference(resolution,[],[f256,f162])).
% 7.57/1.54  fof(f256,plain,(
% 7.57/1.54    ( ! [X4,X5,X3] : (r1_xboole_0(X3,X4) | r2_hidden(sK5(X3,X4),k5_xboole_0(X5,k4_xboole_0(X3,X5)))) )),
% 7.57/1.54    inference(resolution,[],[f156,f75])).
% 7.57/1.54  fof(f75,plain,(
% 7.57/1.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 7.57/1.54    inference(cnf_transformation,[],[f42])).
% 7.57/1.54  fof(f1285,plain,(
% 7.57/1.54    spl8_34 | ~spl8_37 | spl8_35),
% 7.57/1.54    inference(avatar_split_clause,[],[f1276,f1262,f1283,f1259])).
% 7.57/1.54  fof(f1262,plain,(
% 7.57/1.54    spl8_35 <=> r2_hidden(sK3,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1)))),
% 7.57/1.54    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 7.57/1.54  fof(f1276,plain,(
% 7.57/1.54    ~r2_hidden(sK3,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1)))) | r2_hidden(sK3,k1_xboole_0) | spl8_35),
% 7.57/1.54    inference(superposition,[],[f1268,f61])).
% 7.57/1.54  fof(f1268,plain,(
% 7.57/1.54    ( ! [X0] : (~r2_hidden(sK3,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1)),X0))) | r2_hidden(sK3,X0)) ) | spl8_35),
% 7.57/1.54    inference(resolution,[],[f1263,f158])).
% 7.57/1.54  fof(f1263,plain,(
% 7.57/1.54    ~r2_hidden(sK3,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))) | spl8_35),
% 7.57/1.54    inference(avatar_component_clause,[],[f1262])).
% 7.57/1.54  fof(f1264,plain,(
% 7.57/1.54    spl8_34 | ~spl8_35 | spl8_31),
% 7.57/1.54    inference(avatar_split_clause,[],[f1252,f1227,f1262,f1259])).
% 7.57/1.54  fof(f1252,plain,(
% 7.57/1.54    ~r2_hidden(sK3,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))) | r2_hidden(sK3,k1_xboole_0) | spl8_31),
% 7.57/1.54    inference(superposition,[],[f1237,f61])).
% 7.57/1.54  fof(f1237,plain,(
% 7.57/1.54    ( ! [X0] : (~r2_hidden(sK3,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_xboole_0,sK1),X0))) | r2_hidden(sK3,X0)) ) | spl8_31),
% 7.57/1.54    inference(resolution,[],[f1228,f158])).
% 7.57/1.54  fof(f1232,plain,(
% 7.57/1.54    ~spl8_31 | ~spl8_2 | ~spl8_3 | ~spl8_9),
% 7.57/1.54    inference(avatar_split_clause,[],[f1231,f191,f143,f139,f1227])).
% 7.57/1.54  fof(f143,plain,(
% 7.57/1.54    spl8_3 <=> r2_hidden(sK3,sK2)),
% 7.57/1.54    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 7.57/1.54  fof(f1231,plain,(
% 7.57/1.54    ~r2_hidden(sK3,k5_xboole_0(k1_xboole_0,sK1)) | (~spl8_2 | ~spl8_3 | ~spl8_9)),
% 7.57/1.54    inference(forward_demodulation,[],[f1230,f61])).
% 7.57/1.54  fof(f1230,plain,(
% 7.57/1.54    ~r2_hidden(sK3,k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k1_xboole_0))) | (~spl8_2 | ~spl8_3 | ~spl8_9)),
% 7.57/1.54    inference(forward_demodulation,[],[f1220,f213])).
% 7.57/1.54  fof(f213,plain,(
% 7.57/1.54    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4)) ) | (~spl8_2 | ~spl8_9)),
% 7.57/1.54    inference(resolution,[],[f208,f82])).
% 7.57/1.54  fof(f208,plain,(
% 7.57/1.54    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | (~spl8_2 | ~spl8_9)),
% 7.57/1.54    inference(resolution,[],[f203,f75])).
% 7.57/1.54  fof(f1220,plain,(
% 7.57/1.54    ( ! [X2] : (~r2_hidden(sK3,k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)),k4_xboole_0(sK1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)))))) ) | (~spl8_2 | ~spl8_3 | ~spl8_9)),
% 7.57/1.54    inference(resolution,[],[f1214,f211])).
% 7.57/1.54  fof(f211,plain,(
% 7.57/1.54    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))) ) | (~spl8_2 | ~spl8_9)),
% 7.57/1.54    inference(resolution,[],[f208,f117])).
% 7.57/1.54  fof(f1214,plain,(
% 7.57/1.54    ( ! [X3] : (r2_hidden(sK3,X3) | ~r2_hidden(sK3,k5_xboole_0(X3,k4_xboole_0(sK1,X3)))) ) | (~spl8_2 | ~spl8_3)),
% 7.57/1.54    inference(resolution,[],[f1199,f144])).
% 7.57/1.54  fof(f144,plain,(
% 7.57/1.54    r2_hidden(sK3,sK2) | ~spl8_3),
% 7.57/1.54    inference(avatar_component_clause,[],[f143])).
% 7.57/1.54  fof(f1199,plain,(
% 7.57/1.54    ( ! [X12,X13] : (~r2_hidden(X12,sK2) | r2_hidden(X12,X13) | ~r2_hidden(X12,k5_xboole_0(X13,k4_xboole_0(sK1,X13)))) ) | ~spl8_2),
% 7.57/1.54    inference(resolution,[],[f158,f177])).
% 7.57/1.54  fof(f193,plain,(
% 7.57/1.54    spl8_9 | ~spl8_8),
% 7.57/1.54    inference(avatar_split_clause,[],[f189,f185,f191])).
% 7.57/1.54  fof(f185,plain,(
% 7.57/1.54    spl8_8 <=> r1_xboole_0(sK1,sK2)),
% 7.57/1.54    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 7.57/1.54  fof(f189,plain,(
% 7.57/1.54    sK1 = k4_xboole_0(sK1,sK2) | ~spl8_8),
% 7.57/1.54    inference(resolution,[],[f186,f82])).
% 7.57/1.54  fof(f186,plain,(
% 7.57/1.54    r1_xboole_0(sK1,sK2) | ~spl8_8),
% 7.57/1.54    inference(avatar_component_clause,[],[f185])).
% 7.57/1.54  fof(f187,plain,(
% 7.57/1.54    spl8_8 | ~spl8_2),
% 7.57/1.54    inference(avatar_split_clause,[],[f183,f139,f185])).
% 7.57/1.54  fof(f183,plain,(
% 7.57/1.54    r1_xboole_0(sK1,sK2) | ~spl8_2),
% 7.57/1.54    inference(duplicate_literal_removal,[],[f182])).
% 7.57/1.54  fof(f182,plain,(
% 7.57/1.54    r1_xboole_0(sK1,sK2) | r1_xboole_0(sK1,sK2) | ~spl8_2),
% 7.57/1.54    inference(resolution,[],[f179,f76])).
% 7.57/1.54  fof(f179,plain,(
% 7.57/1.54    ( ! [X0] : (~r2_hidden(sK5(sK1,X0),sK2) | r1_xboole_0(sK1,X0)) ) | ~spl8_2),
% 7.57/1.54    inference(resolution,[],[f177,f75])).
% 7.57/1.54  fof(f176,plain,(
% 7.57/1.54    ~spl8_7 | spl8_5),
% 7.57/1.54    inference(avatar_split_clause,[],[f171,f161,f174])).
% 7.57/1.54  fof(f171,plain,(
% 7.57/1.54    k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1) | spl8_5),
% 7.57/1.54    inference(resolution,[],[f83,f162])).
% 7.57/1.54  fof(f83,plain,(
% 7.57/1.54    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 7.57/1.54    inference(cnf_transformation,[],[f47])).
% 7.57/1.54  fof(f163,plain,(
% 7.57/1.54    ~spl8_5 | spl8_1),
% 7.57/1.54    inference(avatar_split_clause,[],[f159,f135,f161])).
% 7.57/1.54  fof(f135,plain,(
% 7.57/1.54    spl8_1 <=> r1_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)),sK1)),
% 7.57/1.54    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 7.57/1.54  fof(f159,plain,(
% 7.57/1.54    ~r1_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK2,sK0)),sK1) | spl8_1),
% 7.57/1.54    inference(forward_demodulation,[],[f136,f113])).
% 7.57/1.54  fof(f136,plain,(
% 7.57/1.54    ~r1_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)),sK1) | spl8_1),
% 7.57/1.54    inference(avatar_component_clause,[],[f135])).
% 7.57/1.54  fof(f149,plain,(
% 7.57/1.54    spl8_4),
% 7.57/1.54    inference(avatar_split_clause,[],[f109,f147])).
% 7.57/1.54  fof(f109,plain,(
% 7.57/1.54    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),
% 7.57/1.54    inference(definition_unfolding,[],[f56,f71,f106])).
% 7.57/1.54  fof(f56,plain,(
% 7.57/1.54    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 7.57/1.54    inference(cnf_transformation,[],[f38])).
% 7.57/1.54  fof(f38,plain,(
% 7.57/1.54    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 7.57/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f37])).
% 7.57/1.54  fof(f37,plain,(
% 7.57/1.54    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 7.57/1.54    introduced(choice_axiom,[])).
% 7.57/1.54  fof(f32,plain,(
% 7.57/1.54    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 7.57/1.54    inference(flattening,[],[f31])).
% 7.57/1.54  fof(f31,plain,(
% 7.57/1.54    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 7.57/1.54    inference(ennf_transformation,[],[f28])).
% 7.57/1.54  fof(f28,negated_conjecture,(
% 7.57/1.54    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 7.57/1.54    inference(negated_conjecture,[],[f27])).
% 7.57/1.54  fof(f27,conjecture,(
% 7.57/1.54    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 7.57/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 7.57/1.54  fof(f145,plain,(
% 7.57/1.54    spl8_3),
% 7.57/1.54    inference(avatar_split_clause,[],[f57,f143])).
% 7.57/1.54  fof(f57,plain,(
% 7.57/1.54    r2_hidden(sK3,sK2)),
% 7.57/1.54    inference(cnf_transformation,[],[f38])).
% 7.57/1.54  fof(f141,plain,(
% 7.57/1.54    spl8_2),
% 7.57/1.54    inference(avatar_split_clause,[],[f58,f139])).
% 7.57/1.54  fof(f58,plain,(
% 7.57/1.54    r1_xboole_0(sK2,sK1)),
% 7.57/1.54    inference(cnf_transformation,[],[f38])).
% 7.57/1.54  fof(f137,plain,(
% 7.57/1.54    ~spl8_1),
% 7.57/1.54    inference(avatar_split_clause,[],[f108,f135])).
% 7.57/1.54  fof(f108,plain,(
% 7.57/1.54    ~r1_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)),sK1)),
% 7.57/1.54    inference(definition_unfolding,[],[f59,f105])).
% 7.57/1.54  fof(f59,plain,(
% 7.57/1.54    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 7.57/1.54    inference(cnf_transformation,[],[f38])).
% 7.57/1.54  % SZS output end Proof for theBenchmark
% 7.57/1.54  % (16080)------------------------------
% 7.57/1.54  % (16080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.57/1.54  % (16080)Termination reason: Refutation
% 7.57/1.54  
% 7.57/1.54  % (16080)Memory used [KB]: 19829
% 7.57/1.54  % (16080)Time elapsed: 0.919 s
% 7.57/1.54  % (16080)------------------------------
% 7.57/1.54  % (16080)------------------------------
% 7.57/1.54  % (15926)Success in time 1.181 s
%------------------------------------------------------------------------------
