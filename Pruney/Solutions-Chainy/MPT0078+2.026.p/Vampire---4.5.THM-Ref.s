%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:50 EST 2020

% Result     : Theorem 10.98s
% Output     : Refutation 10.98s
% Verified   : 
% Statistics : Number of formulae       :  152 (1950 expanded)
%              Number of leaves         :   21 ( 536 expanded)
%              Depth                    :   30
%              Number of atoms          :  298 (6141 expanded)
%              Number of equality atoms :   78 (1307 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48593,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f10567,f40010,f48590])).

fof(f48590,plain,
    ( ~ spl6_19
    | ~ spl6_24 ),
    inference(avatar_contradiction_clause,[],[f48589])).

fof(f48589,plain,
    ( $false
    | ~ spl6_19
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f48535,f44])).

fof(f44,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( sK0 != sK2
    & r1_xboole_0(sK2,sK1)
    & r1_xboole_0(sK0,sK1)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
   => ( sK0 != sK2
      & r1_xboole_0(sK2,sK1)
      & r1_xboole_0(sK0,sK1)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f48535,plain,
    ( sK0 = sK2
    | ~ spl6_19
    | ~ spl6_24 ),
    inference(backward_demodulation,[],[f20354,f48175])).

fof(f48175,plain,
    ( ! [X18] : sK0 = k3_xboole_0(sK0,k2_xboole_0(sK0,X18))
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f48174,f48082])).

fof(f48082,plain,
    ( sK0 = k2_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f48074,f47986])).

fof(f47986,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl6_19 ),
    inference(resolution,[],[f40373,f67])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f40373,plain,
    ( ! [X66] :
        ( ~ r1_tarski(k4_xboole_0(X66,sK2),sK0)
        | r1_tarski(X66,sK0) )
    | ~ spl6_19 ),
    inference(superposition,[],[f64,f20527])).

fof(f20527,plain,
    ( sK0 = k2_xboole_0(sK2,sK0)
    | ~ spl6_19 ),
    inference(superposition,[],[f20350,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f20350,plain,
    ( sK0 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK2))
    | ~ spl6_19 ),
    inference(resolution,[],[f1089,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f1089,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f1088])).

fof(f1088,plain,
    ( spl6_19
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f48074,plain,
    ( sK0 = k2_xboole_0(sK0,k1_xboole_0)
    | ~ r1_tarski(sK0,sK0)
    | ~ spl6_19 ),
    inference(superposition,[],[f59,f48030])).

fof(f48030,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl6_19 ),
    inference(resolution,[],[f47986,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f48174,plain,
    ( ! [X18] : k2_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(sK0,X18))
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f48161,f321])).

fof(f321,plain,(
    ! [X6] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X6) ),
    inference(resolution,[],[f230,f51])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f230,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(resolution,[],[f142,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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

fof(f142,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(resolution,[],[f121,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f121,plain,(
    ! [X1] : r1_xboole_0(k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f74,f91])).

fof(f91,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f73,f51])).

fof(f73,plain,(
    ! [X0] : r1_xboole_0(X0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f69,f46])).

fof(f69,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f42,f49])).

fof(f42,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X1] : r1_xboole_0(k3_xboole_0(sK0,sK1),X1) ),
    inference(resolution,[],[f69,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f48161,plain,
    ( ! [X18] : k2_xboole_0(sK0,k3_xboole_0(k1_xboole_0,X18)) = k3_xboole_0(sK0,k2_xboole_0(sK0,X18))
    | ~ spl6_19 ),
    inference(superposition,[],[f55,f48082])).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f20354,plain,
    ( sK2 = k3_xboole_0(sK0,k2_xboole_0(sK0,sK1))
    | ~ spl6_19
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f20353,f15061])).

fof(f15061,plain,
    ( sK2 = k2_xboole_0(sK2,k1_xboole_0)
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f15057,f61])).

fof(f61,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f15057,plain,
    ( k2_xboole_0(sK2,sK2) = k2_xboole_0(sK2,k1_xboole_0)
    | ~ spl6_24 ),
    inference(superposition,[],[f60,f10695])).

fof(f10695,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK2)
    | ~ spl6_24 ),
    inference(resolution,[],[f1134,f58])).

fof(f1134,plain,
    ( r1_tarski(sK2,sK2)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f1133])).

fof(f1133,plain,
    ( spl6_24
  <=> r1_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f20353,plain,
    ( k2_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(sK0,sK1))
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f20342,f91])).

fof(f20342,plain,
    ( k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,k2_xboole_0(sK0,sK1))
    | ~ spl6_19 ),
    inference(resolution,[],[f1089,f1322])).

fof(f1322,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK2,X1)
      | k3_xboole_0(X1,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK2,k3_xboole_0(X1,sK1)) ) ),
    inference(forward_demodulation,[],[f213,f228])).

fof(f228,plain,(
    ! [X0] : k2_xboole_0(sK2,k3_xboole_0(X0,sK1)) = k2_xboole_0(sK2,k3_xboole_0(k4_xboole_0(X0,sK2),sK1)) ),
    inference(forward_demodulation,[],[f212,f87])).

fof(f87,plain,(
    ! [X2] : k2_xboole_0(sK2,k3_xboole_0(X2,sK1)) = k3_xboole_0(k2_xboole_0(sK2,X2),k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f55,f41])).

fof(f41,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f212,plain,(
    ! [X0] : k3_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK2,k3_xboole_0(k4_xboole_0(X0,sK2),sK1)) ),
    inference(superposition,[],[f87,f60])).

fof(f213,plain,(
    ! [X1] :
      ( k3_xboole_0(X1,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK2,k3_xboole_0(k4_xboole_0(X1,sK2),sK1))
      | ~ r1_tarski(sK2,X1) ) ),
    inference(superposition,[],[f87,f59])).

fof(f40010,plain,
    ( spl6_19
    | ~ spl6_24 ),
    inference(avatar_contradiction_clause,[],[f40009])).

fof(f40009,plain,
    ( $false
    | spl6_19
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f39977,f1090])).

fof(f1090,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl6_19 ),
    inference(avatar_component_clause,[],[f1088])).

fof(f39977,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl6_24 ),
    inference(superposition,[],[f29741,f39841])).

fof(f39841,plain,
    ( sK2 = k3_xboole_0(sK2,k2_xboole_0(sK0,k1_xboole_0))
    | ~ spl6_24 ),
    inference(resolution,[],[f39833,f18362])).

fof(f18362,plain,
    ( ! [X3] :
        ( ~ r1_tarski(sK2,X3)
        | sK2 = k3_xboole_0(sK2,X3) )
    | ~ spl6_24 ),
    inference(superposition,[],[f15250,f59])).

fof(f15250,plain,
    ( ! [X0] : sK2 = k3_xboole_0(sK2,k2_xboole_0(sK2,X0))
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f15249,f15061])).

fof(f15249,plain,
    ( ! [X0] : k2_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK2,k2_xboole_0(sK2,X0))
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f15239,f321])).

fof(f15239,plain,
    ( ! [X0] : k2_xboole_0(sK2,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(sK2,k2_xboole_0(sK2,X0))
    | ~ spl6_24 ),
    inference(superposition,[],[f55,f15061])).

fof(f39833,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK0,k1_xboole_0))
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f39821,f422])).

fof(f422,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f364,f51])).

fof(f364,plain,(
    ! [X0] : r1_xboole_0(X0,k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f362,f46])).

fof(f362,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f361,f49])).

fof(f361,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f360])).

fof(f360,plain,
    ( r1_xboole_0(sK1,sK2)
    | r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f140,f45])).

fof(f140,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0,sK2),sK1)
      | r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f72,f46])).

fof(f72,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f43,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f43,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f39821,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl6_24 ),
    inference(superposition,[],[f36887,f55])).

fof(f36887,plain,
    ( ! [X0] : r1_tarski(sK2,k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(X0,sK2)))
    | ~ spl6_24 ),
    inference(superposition,[],[f21636,f20767])).

fof(f20767,plain,
    ( ! [X5] : sK2 = k3_xboole_0(sK2,k2_xboole_0(X5,sK2))
    | ~ spl6_24 ),
    inference(resolution,[],[f18362,f17095])).

fof(f17095,plain,
    ( ! [X0] : r1_tarski(sK2,k2_xboole_0(X0,sK2))
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f4353,f15061])).

fof(f4353,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(sK2,k1_xboole_0),k2_xboole_0(X0,sK2)) ),
    inference(resolution,[],[f4348,f64])).

fof(f4348,plain,(
    ! [X11] : r1_tarski(k4_xboole_0(k2_xboole_0(sK2,k1_xboole_0),X11),sK2) ),
    inference(resolution,[],[f446,f67])).

fof(f446,plain,(
    ! [X7] :
      ( ~ r1_tarski(X7,k2_xboole_0(sK2,k1_xboole_0))
      | r1_tarski(X7,sK2) ) ),
    inference(superposition,[],[f66,f229])).

fof(f229,plain,(
    k3_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f214,f106])).

fof(f106,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f79,f51])).

fof(f79,plain,(
    ! [X0] : r1_xboole_0(X0,k3_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f71,f46])).

fof(f71,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f43,f49])).

fof(f214,plain,(
    k2_xboole_0(sK2,k3_xboole_0(sK2,sK1)) = k3_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f87,f61])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f21636,plain,
    ( ! [X42] : r1_tarski(k3_xboole_0(sK2,X42),k3_xboole_0(k2_xboole_0(sK0,sK1),X42))
    | ~ spl6_24 ),
    inference(superposition,[],[f629,f15294])).

fof(f15294,plain,
    ( ! [X4] : k3_xboole_0(sK2,k3_xboole_0(k2_xboole_0(sK0,sK1),X4)) = k3_xboole_0(sK2,X4)
    | ~ spl6_24 ),
    inference(superposition,[],[f56,f15232])).

fof(f15232,plain,
    ( sK2 = k3_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl6_24 ),
    inference(backward_demodulation,[],[f229,f15061])).

fof(f56,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f629,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(forward_demodulation,[],[f628,f502])).

fof(f502,plain,(
    ! [X13] : k2_xboole_0(k1_xboole_0,X13) = X13 ),
    inference(forward_demodulation,[],[f492,f62])).

fof(f62,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f492,plain,(
    ! [X13] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X13,k1_xboole_0)) = X13 ),
    inference(resolution,[],[f481,f59])).

fof(f481,plain,(
    ! [X4] : r1_tarski(k1_xboole_0,X4) ),
    inference(superposition,[],[f393,f61])).

fof(f393,plain,(
    ! [X12,X11] : r1_tarski(k1_xboole_0,k2_xboole_0(X11,X12)) ),
    inference(forward_demodulation,[],[f392,f61])).

fof(f392,plain,(
    ! [X12,X11] : r1_tarski(k2_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(X11,X12)) ),
    inference(forward_demodulation,[],[f386,f321])).

fof(f386,plain,(
    ! [X12,X11] : r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X12)),k2_xboole_0(X11,X12)) ),
    inference(superposition,[],[f65,f321])).

fof(f65,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f628,plain,(
    ! [X2,X1] : r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(X2,X1)),X1) ),
    inference(forward_demodulation,[],[f621,f63])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f621,plain,(
    ! [X2,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X2,k1_xboole_0),k3_xboole_0(X2,X1)),X1) ),
    inference(superposition,[],[f65,f502])).

fof(f29741,plain,(
    ! [X14,X15] : r1_tarski(k3_xboole_0(X14,k2_xboole_0(X15,k1_xboole_0)),X15) ),
    inference(resolution,[],[f29692,f2855])).

fof(f2855,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,X4)
      | r1_tarski(k3_xboole_0(X5,X3),X4) ) ),
    inference(superposition,[],[f2595,f59])).

fof(f2595,plain,(
    ! [X4,X2,X3] : r1_tarski(k3_xboole_0(X2,X3),k2_xboole_0(X3,X4)) ),
    inference(subsumption_resolution,[],[f2584,f481])).

fof(f2584,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k1_xboole_0,X4)
      | r1_tarski(k3_xboole_0(X2,X3),k2_xboole_0(X3,X4)) ) ),
    inference(superposition,[],[f64,f640])).

fof(f640,plain,(
    ! [X19,X18] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X18,X19),X19) ),
    inference(resolution,[],[f629,f58])).

fof(f29692,plain,(
    ! [X4] : r1_tarski(k2_xboole_0(X4,k1_xboole_0),X4) ),
    inference(superposition,[],[f29540,f61])).

fof(f29540,plain,(
    ! [X41,X40] : r1_tarski(k2_xboole_0(X41,k1_xboole_0),k2_xboole_0(X41,X40)) ),
    inference(superposition,[],[f648,f321])).

fof(f648,plain,(
    ! [X12,X10,X11] : r1_tarski(k2_xboole_0(X10,k3_xboole_0(X11,X12)),k2_xboole_0(X10,X12)) ),
    inference(superposition,[],[f629,f55])).

fof(f10567,plain,(
    spl6_24 ),
    inference(avatar_contradiction_clause,[],[f10566])).

fof(f10566,plain,
    ( $false
    | spl6_24 ),
    inference(subsumption_resolution,[],[f10560,f1135])).

fof(f1135,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl6_24 ),
    inference(avatar_component_clause,[],[f1133])).

fof(f10560,plain,(
    r1_tarski(sK2,sK2) ),
    inference(superposition,[],[f10508,f61])).

fof(f10508,plain,(
    ! [X3] : r1_tarski(sK2,k2_xboole_0(sK2,X3)) ),
    inference(superposition,[],[f10489,f62])).

fof(f10489,plain,(
    ! [X26,X27] : r1_tarski(k4_xboole_0(sK2,X26),k2_xboole_0(sK2,X27)) ),
    inference(resolution,[],[f10442,f67])).

fof(f10442,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK2)
      | r1_tarski(X0,k2_xboole_0(sK2,X1)) ) ),
    inference(subsumption_resolution,[],[f10430,f481])).

fof(f10430,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,k3_xboole_0(X1,sK1))
      | r1_tarski(X0,k2_xboole_0(sK2,X1))
      | ~ r1_tarski(X0,sK2) ) ),
    inference(superposition,[],[f718,f58])).

fof(f718,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,sK2),k3_xboole_0(X1,sK1))
      | r1_tarski(X0,k2_xboole_0(sK2,X1)) ) ),
    inference(resolution,[],[f226,f64])).

fof(f226,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X16,k2_xboole_0(sK2,k3_xboole_0(X15,sK1)))
      | r1_tarski(X16,k2_xboole_0(sK2,X15)) ) ),
    inference(superposition,[],[f66,f87])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (26784)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (26779)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (26783)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (26787)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  % (26792)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (26781)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (26778)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (26790)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (26793)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.49  % (26785)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (26782)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (26789)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (26780)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (26798)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (26791)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (26788)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (26794)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.51  % (26795)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % (26786)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.51  % (26799)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (26797)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (26799)Refutation not found, incomplete strategy% (26799)------------------------------
% 0.20/0.51  % (26799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26799)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (26799)Memory used [KB]: 10618
% 0.20/0.51  % (26799)Time elapsed: 0.106 s
% 0.20/0.51  % (26799)------------------------------
% 0.20/0.51  % (26799)------------------------------
% 3.68/0.91  % (26790)Time limit reached!
% 3.68/0.91  % (26790)------------------------------
% 3.68/0.91  % (26790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.42/0.92  % (26783)Time limit reached!
% 4.42/0.92  % (26783)------------------------------
% 4.42/0.92  % (26783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.42/0.92  % (26783)Termination reason: Time limit
% 4.42/0.92  % (26783)Termination phase: Saturation
% 4.42/0.92  
% 4.42/0.92  % (26783)Memory used [KB]: 7803
% 4.42/0.92  % (26783)Time elapsed: 0.500 s
% 4.42/0.92  % (26783)------------------------------
% 4.42/0.92  % (26783)------------------------------
% 4.42/0.92  % (26790)Termination reason: Time limit
% 4.42/0.92  
% 4.42/0.92  % (26790)Memory used [KB]: 13048
% 4.42/0.92  % (26790)Time elapsed: 0.511 s
% 4.42/0.92  % (26790)------------------------------
% 4.42/0.92  % (26790)------------------------------
% 4.42/0.92  % (26788)Time limit reached!
% 4.42/0.92  % (26788)------------------------------
% 4.42/0.92  % (26788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.42/0.92  % (26788)Termination reason: Time limit
% 4.42/0.92  
% 4.42/0.92  % (26788)Memory used [KB]: 12153
% 4.42/0.92  % (26788)Time elapsed: 0.516 s
% 4.42/0.92  % (26788)------------------------------
% 4.42/0.92  % (26788)------------------------------
% 4.42/0.92  % (26779)Time limit reached!
% 4.42/0.92  % (26779)------------------------------
% 4.42/0.92  % (26779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.42/0.92  % (26779)Termination reason: Time limit
% 4.42/0.92  % (26779)Termination phase: Saturation
% 4.42/0.92  
% 4.42/0.92  % (26779)Memory used [KB]: 18166
% 4.42/0.92  % (26779)Time elapsed: 0.500 s
% 4.42/0.92  % (26779)------------------------------
% 4.42/0.92  % (26779)------------------------------
% 4.42/0.94  % (26778)Time limit reached!
% 4.42/0.94  % (26778)------------------------------
% 4.42/0.94  % (26778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.42/0.94  % (26778)Termination reason: Time limit
% 4.42/0.94  % (26778)Termination phase: Saturation
% 4.42/0.94  
% 4.42/0.94  % (26778)Memory used [KB]: 12792
% 4.42/0.94  % (26778)Time elapsed: 0.500 s
% 4.42/0.94  % (26778)------------------------------
% 4.42/0.94  % (26778)------------------------------
% 5.05/1.03  % (26786)Time limit reached!
% 5.05/1.03  % (26786)------------------------------
% 5.05/1.03  % (26786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.05/1.03  % (26786)Termination reason: Time limit
% 5.05/1.03  
% 5.05/1.03  % (26786)Memory used [KB]: 12792
% 5.05/1.03  % (26786)Time elapsed: 0.617 s
% 5.05/1.03  % (26786)------------------------------
% 5.05/1.03  % (26786)------------------------------
% 7.44/1.34  % (26787)Time limit reached!
% 7.44/1.34  % (26787)------------------------------
% 7.44/1.34  % (26787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.44/1.34  % (26787)Termination reason: Time limit
% 7.44/1.34  % (26787)Termination phase: Saturation
% 7.44/1.34  
% 7.44/1.34  % (26787)Memory used [KB]: 22003
% 7.44/1.34  % (26787)Time elapsed: 0.900 s
% 7.44/1.34  % (26787)------------------------------
% 7.44/1.34  % (26787)------------------------------
% 9.19/1.52  % (26780)Time limit reached!
% 9.19/1.52  % (26780)------------------------------
% 9.19/1.52  % (26780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.19/1.52  % (26780)Termination reason: Time limit
% 9.19/1.52  % (26780)Termination phase: Saturation
% 9.19/1.52  
% 9.19/1.52  % (26780)Memory used [KB]: 23411
% 9.19/1.52  % (26780)Time elapsed: 1.100 s
% 9.19/1.52  % (26780)------------------------------
% 9.19/1.52  % (26780)------------------------------
% 10.70/1.71  % (26781)Time limit reached!
% 10.70/1.71  % (26781)------------------------------
% 10.70/1.71  % (26781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.70/1.71  % (26781)Termination reason: Time limit
% 10.70/1.71  % (26781)Termination phase: Saturation
% 10.70/1.71  
% 10.70/1.71  % (26781)Memory used [KB]: 40937
% 10.70/1.71  % (26781)Time elapsed: 1.300 s
% 10.70/1.71  % (26781)------------------------------
% 10.70/1.71  % (26781)------------------------------
% 10.98/1.78  % (26798)Refutation found. Thanks to Tanya!
% 10.98/1.78  % SZS status Theorem for theBenchmark
% 10.98/1.78  % SZS output start Proof for theBenchmark
% 10.98/1.78  fof(f48593,plain,(
% 10.98/1.78    $false),
% 10.98/1.78    inference(avatar_sat_refutation,[],[f10567,f40010,f48590])).
% 10.98/1.78  fof(f48590,plain,(
% 10.98/1.78    ~spl6_19 | ~spl6_24),
% 10.98/1.78    inference(avatar_contradiction_clause,[],[f48589])).
% 10.98/1.78  fof(f48589,plain,(
% 10.98/1.78    $false | (~spl6_19 | ~spl6_24)),
% 10.98/1.78    inference(subsumption_resolution,[],[f48535,f44])).
% 10.98/1.78  fof(f44,plain,(
% 10.98/1.78    sK0 != sK2),
% 10.98/1.78    inference(cnf_transformation,[],[f33])).
% 10.98/1.78  fof(f33,plain,(
% 10.98/1.78    sK0 != sK2 & r1_xboole_0(sK2,sK1) & r1_xboole_0(sK0,sK1) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 10.98/1.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f32])).
% 10.98/1.78  fof(f32,plain,(
% 10.98/1.78    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => (sK0 != sK2 & r1_xboole_0(sK2,sK1) & r1_xboole_0(sK0,sK1) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1))),
% 10.98/1.78    introduced(choice_axiom,[])).
% 10.98/1.78  fof(f23,plain,(
% 10.98/1.78    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 10.98/1.78    inference(flattening,[],[f22])).
% 10.98/1.78  fof(f22,plain,(
% 10.98/1.78    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 10.98/1.78    inference(ennf_transformation,[],[f18])).
% 10.98/1.78  fof(f18,negated_conjecture,(
% 10.98/1.78    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 10.98/1.78    inference(negated_conjecture,[],[f17])).
% 10.98/1.78  fof(f17,conjecture,(
% 10.98/1.78    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 10.98/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).
% 10.98/1.78  fof(f48535,plain,(
% 10.98/1.78    sK0 = sK2 | (~spl6_19 | ~spl6_24)),
% 10.98/1.78    inference(backward_demodulation,[],[f20354,f48175])).
% 10.98/1.78  fof(f48175,plain,(
% 10.98/1.78    ( ! [X18] : (sK0 = k3_xboole_0(sK0,k2_xboole_0(sK0,X18))) ) | ~spl6_19),
% 10.98/1.78    inference(forward_demodulation,[],[f48174,f48082])).
% 10.98/1.78  fof(f48082,plain,(
% 10.98/1.78    sK0 = k2_xboole_0(sK0,k1_xboole_0) | ~spl6_19),
% 10.98/1.78    inference(subsumption_resolution,[],[f48074,f47986])).
% 10.98/1.78  fof(f47986,plain,(
% 10.98/1.78    r1_tarski(sK0,sK0) | ~spl6_19),
% 10.98/1.78    inference(resolution,[],[f40373,f67])).
% 10.98/1.78  fof(f67,plain,(
% 10.98/1.78    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 10.98/1.78    inference(cnf_transformation,[],[f10])).
% 10.98/1.78  fof(f10,axiom,(
% 10.98/1.78    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 10.98/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 10.98/1.78  fof(f40373,plain,(
% 10.98/1.78    ( ! [X66] : (~r1_tarski(k4_xboole_0(X66,sK2),sK0) | r1_tarski(X66,sK0)) ) | ~spl6_19),
% 10.98/1.78    inference(superposition,[],[f64,f20527])).
% 10.98/1.78  fof(f20527,plain,(
% 10.98/1.78    sK0 = k2_xboole_0(sK2,sK0) | ~spl6_19),
% 10.98/1.78    inference(superposition,[],[f20350,f60])).
% 10.98/1.78  fof(f60,plain,(
% 10.98/1.78    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 10.98/1.78    inference(cnf_transformation,[],[f12])).
% 10.98/1.78  fof(f12,axiom,(
% 10.98/1.78    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 10.98/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 10.98/1.78  fof(f20350,plain,(
% 10.98/1.78    sK0 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK2)) | ~spl6_19),
% 10.98/1.78    inference(resolution,[],[f1089,f59])).
% 10.98/1.78  fof(f59,plain,(
% 10.98/1.78    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 10.98/1.78    inference(cnf_transformation,[],[f29])).
% 10.98/1.78  fof(f29,plain,(
% 10.98/1.78    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 10.98/1.78    inference(ennf_transformation,[],[f15])).
% 10.98/1.78  fof(f15,axiom,(
% 10.98/1.78    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 10.98/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 10.98/1.78  fof(f1089,plain,(
% 10.98/1.78    r1_tarski(sK2,sK0) | ~spl6_19),
% 10.98/1.78    inference(avatar_component_clause,[],[f1088])).
% 10.98/1.78  fof(f1088,plain,(
% 10.98/1.78    spl6_19 <=> r1_tarski(sK2,sK0)),
% 10.98/1.78    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 10.98/1.78  fof(f64,plain,(
% 10.98/1.78    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 10.98/1.78    inference(cnf_transformation,[],[f30])).
% 10.98/1.78  fof(f30,plain,(
% 10.98/1.78    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 10.98/1.78    inference(ennf_transformation,[],[f14])).
% 10.98/1.78  fof(f14,axiom,(
% 10.98/1.78    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 10.98/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 10.98/1.78  fof(f48074,plain,(
% 10.98/1.78    sK0 = k2_xboole_0(sK0,k1_xboole_0) | ~r1_tarski(sK0,sK0) | ~spl6_19),
% 10.98/1.78    inference(superposition,[],[f59,f48030])).
% 10.98/1.78  fof(f48030,plain,(
% 10.98/1.78    k1_xboole_0 = k4_xboole_0(sK0,sK0) | ~spl6_19),
% 10.98/1.78    inference(resolution,[],[f47986,f58])).
% 10.98/1.78  fof(f58,plain,(
% 10.98/1.78    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 10.98/1.78    inference(cnf_transformation,[],[f40])).
% 10.98/1.78  fof(f40,plain,(
% 10.98/1.78    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 10.98/1.78    inference(nnf_transformation,[],[f11])).
% 10.98/1.78  fof(f11,axiom,(
% 10.98/1.78    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 10.98/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).
% 10.98/1.78  fof(f48174,plain,(
% 10.98/1.78    ( ! [X18] : (k2_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(sK0,X18))) ) | ~spl6_19),
% 10.98/1.78    inference(forward_demodulation,[],[f48161,f321])).
% 10.98/1.78  fof(f321,plain,(
% 10.98/1.78    ( ! [X6] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X6)) )),
% 10.98/1.78    inference(resolution,[],[f230,f51])).
% 10.98/1.78  fof(f51,plain,(
% 10.98/1.78    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 10.98/1.78    inference(cnf_transformation,[],[f26])).
% 10.98/1.78  fof(f26,plain,(
% 10.98/1.78    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 10.98/1.78    inference(ennf_transformation,[],[f16])).
% 10.98/1.78  fof(f16,axiom,(
% 10.98/1.78    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 10.98/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 10.98/1.78  fof(f230,plain,(
% 10.98/1.78    ( ! [X0,X1] : (r1_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1))) )),
% 10.98/1.78    inference(resolution,[],[f142,f46])).
% 10.98/1.78  fof(f46,plain,(
% 10.98/1.78    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 10.98/1.78    inference(cnf_transformation,[],[f35])).
% 10.98/1.78  fof(f35,plain,(
% 10.98/1.78    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 10.98/1.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f34])).
% 10.98/1.78  fof(f34,plain,(
% 10.98/1.78    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 10.98/1.78    introduced(choice_axiom,[])).
% 10.98/1.78  fof(f24,plain,(
% 10.98/1.78    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 10.98/1.78    inference(ennf_transformation,[],[f19])).
% 10.98/1.78  fof(f19,plain,(
% 10.98/1.78    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 10.98/1.78    inference(rectify,[],[f2])).
% 10.98/1.78  fof(f2,axiom,(
% 10.98/1.78    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 10.98/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 10.98/1.78  fof(f142,plain,(
% 10.98/1.78    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1))) )),
% 10.98/1.78    inference(resolution,[],[f121,f49])).
% 10.98/1.78  fof(f49,plain,(
% 10.98/1.78    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 10.98/1.78    inference(cnf_transformation,[],[f37])).
% 10.98/1.78  fof(f37,plain,(
% 10.98/1.78    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 10.98/1.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f36])).
% 10.98/1.78  fof(f36,plain,(
% 10.98/1.78    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 10.98/1.78    introduced(choice_axiom,[])).
% 10.98/1.78  fof(f25,plain,(
% 10.98/1.78    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 10.98/1.78    inference(ennf_transformation,[],[f20])).
% 10.98/1.78  fof(f20,plain,(
% 10.98/1.78    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 10.98/1.78    inference(rectify,[],[f3])).
% 10.98/1.78  fof(f3,axiom,(
% 10.98/1.78    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 10.98/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 10.98/1.78  fof(f121,plain,(
% 10.98/1.78    ( ! [X1] : (r1_xboole_0(k1_xboole_0,X1)) )),
% 10.98/1.78    inference(backward_demodulation,[],[f74,f91])).
% 10.98/1.78  fof(f91,plain,(
% 10.98/1.78    k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 10.98/1.78    inference(resolution,[],[f73,f51])).
% 10.98/1.78  fof(f73,plain,(
% 10.98/1.78    ( ! [X0] : (r1_xboole_0(X0,k3_xboole_0(sK0,sK1))) )),
% 10.98/1.78    inference(resolution,[],[f69,f46])).
% 10.98/1.78  fof(f69,plain,(
% 10.98/1.78    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,sK1))) )),
% 10.98/1.78    inference(resolution,[],[f42,f49])).
% 10.98/1.78  fof(f42,plain,(
% 10.98/1.78    r1_xboole_0(sK0,sK1)),
% 10.98/1.78    inference(cnf_transformation,[],[f33])).
% 10.98/1.78  fof(f74,plain,(
% 10.98/1.78    ( ! [X1] : (r1_xboole_0(k3_xboole_0(sK0,sK1),X1)) )),
% 10.98/1.78    inference(resolution,[],[f69,f45])).
% 10.98/1.78  fof(f45,plain,(
% 10.98/1.78    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 10.98/1.78    inference(cnf_transformation,[],[f35])).
% 10.98/1.78  fof(f48161,plain,(
% 10.98/1.78    ( ! [X18] : (k2_xboole_0(sK0,k3_xboole_0(k1_xboole_0,X18)) = k3_xboole_0(sK0,k2_xboole_0(sK0,X18))) ) | ~spl6_19),
% 10.98/1.78    inference(superposition,[],[f55,f48082])).
% 10.98/1.78  fof(f55,plain,(
% 10.98/1.78    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 10.98/1.78    inference(cnf_transformation,[],[f7])).
% 10.98/1.78  fof(f7,axiom,(
% 10.98/1.78    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 10.98/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).
% 10.98/1.78  fof(f20354,plain,(
% 10.98/1.78    sK2 = k3_xboole_0(sK0,k2_xboole_0(sK0,sK1)) | (~spl6_19 | ~spl6_24)),
% 10.98/1.78    inference(forward_demodulation,[],[f20353,f15061])).
% 10.98/1.78  fof(f15061,plain,(
% 10.98/1.78    sK2 = k2_xboole_0(sK2,k1_xboole_0) | ~spl6_24),
% 10.98/1.78    inference(forward_demodulation,[],[f15057,f61])).
% 10.98/1.78  fof(f61,plain,(
% 10.98/1.78    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 10.98/1.78    inference(cnf_transformation,[],[f21])).
% 10.98/1.78  fof(f21,plain,(
% 10.98/1.78    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 10.98/1.78    inference(rectify,[],[f1])).
% 10.98/1.78  fof(f1,axiom,(
% 10.98/1.78    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 10.98/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 10.98/1.78  fof(f15057,plain,(
% 10.98/1.78    k2_xboole_0(sK2,sK2) = k2_xboole_0(sK2,k1_xboole_0) | ~spl6_24),
% 10.98/1.78    inference(superposition,[],[f60,f10695])).
% 10.98/1.78  fof(f10695,plain,(
% 10.98/1.78    k1_xboole_0 = k4_xboole_0(sK2,sK2) | ~spl6_24),
% 10.98/1.78    inference(resolution,[],[f1134,f58])).
% 10.98/1.78  fof(f1134,plain,(
% 10.98/1.78    r1_tarski(sK2,sK2) | ~spl6_24),
% 10.98/1.78    inference(avatar_component_clause,[],[f1133])).
% 10.98/1.78  fof(f1133,plain,(
% 10.98/1.78    spl6_24 <=> r1_tarski(sK2,sK2)),
% 10.98/1.78    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 10.98/1.78  fof(f20353,plain,(
% 10.98/1.78    k2_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(sK0,sK1)) | ~spl6_19),
% 10.98/1.78    inference(forward_demodulation,[],[f20342,f91])).
% 10.98/1.78  fof(f20342,plain,(
% 10.98/1.78    k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,k2_xboole_0(sK0,sK1)) | ~spl6_19),
% 10.98/1.78    inference(resolution,[],[f1089,f1322])).
% 10.98/1.78  fof(f1322,plain,(
% 10.98/1.78    ( ! [X1] : (~r1_tarski(sK2,X1) | k3_xboole_0(X1,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK2,k3_xboole_0(X1,sK1))) )),
% 10.98/1.78    inference(forward_demodulation,[],[f213,f228])).
% 10.98/1.78  fof(f228,plain,(
% 10.98/1.78    ( ! [X0] : (k2_xboole_0(sK2,k3_xboole_0(X0,sK1)) = k2_xboole_0(sK2,k3_xboole_0(k4_xboole_0(X0,sK2),sK1))) )),
% 10.98/1.78    inference(forward_demodulation,[],[f212,f87])).
% 10.98/1.78  fof(f87,plain,(
% 10.98/1.78    ( ! [X2] : (k2_xboole_0(sK2,k3_xboole_0(X2,sK1)) = k3_xboole_0(k2_xboole_0(sK2,X2),k2_xboole_0(sK0,sK1))) )),
% 10.98/1.78    inference(superposition,[],[f55,f41])).
% 10.98/1.78  fof(f41,plain,(
% 10.98/1.78    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 10.98/1.78    inference(cnf_transformation,[],[f33])).
% 10.98/1.78  fof(f212,plain,(
% 10.98/1.78    ( ! [X0] : (k3_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK2,k3_xboole_0(k4_xboole_0(X0,sK2),sK1))) )),
% 10.98/1.78    inference(superposition,[],[f87,f60])).
% 10.98/1.78  fof(f213,plain,(
% 10.98/1.78    ( ! [X1] : (k3_xboole_0(X1,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK2,k3_xboole_0(k4_xboole_0(X1,sK2),sK1)) | ~r1_tarski(sK2,X1)) )),
% 10.98/1.78    inference(superposition,[],[f87,f59])).
% 10.98/1.78  fof(f40010,plain,(
% 10.98/1.78    spl6_19 | ~spl6_24),
% 10.98/1.78    inference(avatar_contradiction_clause,[],[f40009])).
% 10.98/1.78  fof(f40009,plain,(
% 10.98/1.78    $false | (spl6_19 | ~spl6_24)),
% 10.98/1.78    inference(subsumption_resolution,[],[f39977,f1090])).
% 10.98/1.78  fof(f1090,plain,(
% 10.98/1.78    ~r1_tarski(sK2,sK0) | spl6_19),
% 10.98/1.78    inference(avatar_component_clause,[],[f1088])).
% 10.98/1.78  fof(f39977,plain,(
% 10.98/1.78    r1_tarski(sK2,sK0) | ~spl6_24),
% 10.98/1.78    inference(superposition,[],[f29741,f39841])).
% 10.98/1.78  fof(f39841,plain,(
% 10.98/1.78    sK2 = k3_xboole_0(sK2,k2_xboole_0(sK0,k1_xboole_0)) | ~spl6_24),
% 10.98/1.78    inference(resolution,[],[f39833,f18362])).
% 10.98/1.78  fof(f18362,plain,(
% 10.98/1.78    ( ! [X3] : (~r1_tarski(sK2,X3) | sK2 = k3_xboole_0(sK2,X3)) ) | ~spl6_24),
% 10.98/1.78    inference(superposition,[],[f15250,f59])).
% 10.98/1.78  fof(f15250,plain,(
% 10.98/1.78    ( ! [X0] : (sK2 = k3_xboole_0(sK2,k2_xboole_0(sK2,X0))) ) | ~spl6_24),
% 10.98/1.78    inference(forward_demodulation,[],[f15249,f15061])).
% 10.98/1.78  fof(f15249,plain,(
% 10.98/1.78    ( ! [X0] : (k2_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK2,k2_xboole_0(sK2,X0))) ) | ~spl6_24),
% 10.98/1.78    inference(forward_demodulation,[],[f15239,f321])).
% 10.98/1.78  fof(f15239,plain,(
% 10.98/1.78    ( ! [X0] : (k2_xboole_0(sK2,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(sK2,k2_xboole_0(sK2,X0))) ) | ~spl6_24),
% 10.98/1.78    inference(superposition,[],[f55,f15061])).
% 10.98/1.78  fof(f39833,plain,(
% 10.98/1.78    r1_tarski(sK2,k2_xboole_0(sK0,k1_xboole_0)) | ~spl6_24),
% 10.98/1.78    inference(forward_demodulation,[],[f39821,f422])).
% 10.98/1.78  fof(f422,plain,(
% 10.98/1.78    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 10.98/1.78    inference(resolution,[],[f364,f51])).
% 10.98/1.78  fof(f364,plain,(
% 10.98/1.78    ( ! [X0] : (r1_xboole_0(X0,k3_xboole_0(sK1,sK2))) )),
% 10.98/1.78    inference(resolution,[],[f362,f46])).
% 10.98/1.78  fof(f362,plain,(
% 10.98/1.78    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,sK2))) )),
% 10.98/1.78    inference(resolution,[],[f361,f49])).
% 10.98/1.78  fof(f361,plain,(
% 10.98/1.78    r1_xboole_0(sK1,sK2)),
% 10.98/1.78    inference(duplicate_literal_removal,[],[f360])).
% 10.98/1.78  fof(f360,plain,(
% 10.98/1.78    r1_xboole_0(sK1,sK2) | r1_xboole_0(sK1,sK2)),
% 10.98/1.78    inference(resolution,[],[f140,f45])).
% 10.98/1.78  fof(f140,plain,(
% 10.98/1.78    ( ! [X0] : (~r2_hidden(sK3(X0,sK2),sK1) | r1_xboole_0(X0,sK2)) )),
% 10.98/1.78    inference(resolution,[],[f72,f46])).
% 10.98/1.78  fof(f72,plain,(
% 10.98/1.78    ( ! [X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1)) )),
% 10.98/1.78    inference(resolution,[],[f43,f47])).
% 10.98/1.78  fof(f47,plain,(
% 10.98/1.78    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 10.98/1.78    inference(cnf_transformation,[],[f35])).
% 10.98/1.78  fof(f43,plain,(
% 10.98/1.78    r1_xboole_0(sK2,sK1)),
% 10.98/1.78    inference(cnf_transformation,[],[f33])).
% 10.98/1.78  fof(f39821,plain,(
% 10.98/1.78    r1_tarski(sK2,k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))) | ~spl6_24),
% 10.98/1.78    inference(superposition,[],[f36887,f55])).
% 10.98/1.78  fof(f36887,plain,(
% 10.98/1.78    ( ! [X0] : (r1_tarski(sK2,k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(X0,sK2)))) ) | ~spl6_24),
% 10.98/1.78    inference(superposition,[],[f21636,f20767])).
% 10.98/1.78  fof(f20767,plain,(
% 10.98/1.78    ( ! [X5] : (sK2 = k3_xboole_0(sK2,k2_xboole_0(X5,sK2))) ) | ~spl6_24),
% 10.98/1.78    inference(resolution,[],[f18362,f17095])).
% 10.98/1.78  fof(f17095,plain,(
% 10.98/1.78    ( ! [X0] : (r1_tarski(sK2,k2_xboole_0(X0,sK2))) ) | ~spl6_24),
% 10.98/1.78    inference(forward_demodulation,[],[f4353,f15061])).
% 10.98/1.78  fof(f4353,plain,(
% 10.98/1.78    ( ! [X0] : (r1_tarski(k2_xboole_0(sK2,k1_xboole_0),k2_xboole_0(X0,sK2))) )),
% 10.98/1.78    inference(resolution,[],[f4348,f64])).
% 10.98/1.78  fof(f4348,plain,(
% 10.98/1.78    ( ! [X11] : (r1_tarski(k4_xboole_0(k2_xboole_0(sK2,k1_xboole_0),X11),sK2)) )),
% 10.98/1.78    inference(resolution,[],[f446,f67])).
% 10.98/1.78  fof(f446,plain,(
% 10.98/1.78    ( ! [X7] : (~r1_tarski(X7,k2_xboole_0(sK2,k1_xboole_0)) | r1_tarski(X7,sK2)) )),
% 10.98/1.78    inference(superposition,[],[f66,f229])).
% 10.98/1.78  fof(f229,plain,(
% 10.98/1.78    k3_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK2,k1_xboole_0)),
% 10.98/1.78    inference(forward_demodulation,[],[f214,f106])).
% 10.98/1.78  fof(f106,plain,(
% 10.98/1.78    k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 10.98/1.78    inference(resolution,[],[f79,f51])).
% 10.98/1.78  fof(f79,plain,(
% 10.98/1.78    ( ! [X0] : (r1_xboole_0(X0,k3_xboole_0(sK2,sK1))) )),
% 10.98/1.78    inference(resolution,[],[f71,f46])).
% 10.98/1.78  fof(f71,plain,(
% 10.98/1.78    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK2,sK1))) )),
% 10.98/1.78    inference(resolution,[],[f43,f49])).
% 10.98/1.78  fof(f214,plain,(
% 10.98/1.78    k2_xboole_0(sK2,k3_xboole_0(sK2,sK1)) = k3_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 10.98/1.78    inference(superposition,[],[f87,f61])).
% 10.98/1.78  fof(f66,plain,(
% 10.98/1.78    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 10.98/1.78    inference(cnf_transformation,[],[f31])).
% 10.98/1.78  fof(f31,plain,(
% 10.98/1.78    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 10.98/1.78    inference(ennf_transformation,[],[f5])).
% 10.98/1.78  fof(f5,axiom,(
% 10.98/1.78    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 10.98/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 10.98/1.78  fof(f21636,plain,(
% 10.98/1.78    ( ! [X42] : (r1_tarski(k3_xboole_0(sK2,X42),k3_xboole_0(k2_xboole_0(sK0,sK1),X42))) ) | ~spl6_24),
% 10.98/1.78    inference(superposition,[],[f629,f15294])).
% 10.98/1.78  fof(f15294,plain,(
% 10.98/1.78    ( ! [X4] : (k3_xboole_0(sK2,k3_xboole_0(k2_xboole_0(sK0,sK1),X4)) = k3_xboole_0(sK2,X4)) ) | ~spl6_24),
% 10.98/1.78    inference(superposition,[],[f56,f15232])).
% 10.98/1.78  fof(f15232,plain,(
% 10.98/1.78    sK2 = k3_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | ~spl6_24),
% 10.98/1.78    inference(backward_demodulation,[],[f229,f15061])).
% 10.98/1.78  fof(f56,plain,(
% 10.98/1.78    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 10.98/1.78    inference(cnf_transformation,[],[f4])).
% 10.98/1.78  fof(f4,axiom,(
% 10.98/1.78    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 10.98/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 10.98/1.78  fof(f629,plain,(
% 10.98/1.78    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 10.98/1.78    inference(forward_demodulation,[],[f628,f502])).
% 10.98/1.78  fof(f502,plain,(
% 10.98/1.78    ( ! [X13] : (k2_xboole_0(k1_xboole_0,X13) = X13) )),
% 10.98/1.78    inference(forward_demodulation,[],[f492,f62])).
% 10.98/1.78  fof(f62,plain,(
% 10.98/1.78    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 10.98/1.78    inference(cnf_transformation,[],[f13])).
% 10.98/1.78  fof(f13,axiom,(
% 10.98/1.78    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 10.98/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 10.98/1.78  fof(f492,plain,(
% 10.98/1.78    ( ! [X13] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X13,k1_xboole_0)) = X13) )),
% 10.98/1.78    inference(resolution,[],[f481,f59])).
% 10.98/1.78  fof(f481,plain,(
% 10.98/1.78    ( ! [X4] : (r1_tarski(k1_xboole_0,X4)) )),
% 10.98/1.78    inference(superposition,[],[f393,f61])).
% 10.98/1.78  fof(f393,plain,(
% 10.98/1.78    ( ! [X12,X11] : (r1_tarski(k1_xboole_0,k2_xboole_0(X11,X12))) )),
% 10.98/1.78    inference(forward_demodulation,[],[f392,f61])).
% 10.98/1.78  fof(f392,plain,(
% 10.98/1.78    ( ! [X12,X11] : (r1_tarski(k2_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(X11,X12))) )),
% 10.98/1.78    inference(forward_demodulation,[],[f386,f321])).
% 10.98/1.78  fof(f386,plain,(
% 10.98/1.78    ( ! [X12,X11] : (r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X12)),k2_xboole_0(X11,X12))) )),
% 10.98/1.78    inference(superposition,[],[f65,f321])).
% 10.98/1.78  fof(f65,plain,(
% 10.98/1.78    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 10.98/1.78    inference(cnf_transformation,[],[f9])).
% 10.98/1.78  fof(f9,axiom,(
% 10.98/1.78    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 10.98/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 10.98/1.78  fof(f628,plain,(
% 10.98/1.78    ( ! [X2,X1] : (r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(X2,X1)),X1)) )),
% 10.98/1.78    inference(forward_demodulation,[],[f621,f63])).
% 10.98/1.78  fof(f63,plain,(
% 10.98/1.78    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 10.98/1.78    inference(cnf_transformation,[],[f8])).
% 10.98/1.78  fof(f8,axiom,(
% 10.98/1.78    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 10.98/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 10.98/1.78  fof(f621,plain,(
% 10.98/1.78    ( ! [X2,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X2,k1_xboole_0),k3_xboole_0(X2,X1)),X1)) )),
% 10.98/1.78    inference(superposition,[],[f65,f502])).
% 10.98/1.78  fof(f29741,plain,(
% 10.98/1.78    ( ! [X14,X15] : (r1_tarski(k3_xboole_0(X14,k2_xboole_0(X15,k1_xboole_0)),X15)) )),
% 10.98/1.78    inference(resolution,[],[f29692,f2855])).
% 10.98/1.78  fof(f2855,plain,(
% 10.98/1.78    ( ! [X4,X5,X3] : (~r1_tarski(X3,X4) | r1_tarski(k3_xboole_0(X5,X3),X4)) )),
% 10.98/1.78    inference(superposition,[],[f2595,f59])).
% 10.98/1.78  fof(f2595,plain,(
% 10.98/1.78    ( ! [X4,X2,X3] : (r1_tarski(k3_xboole_0(X2,X3),k2_xboole_0(X3,X4))) )),
% 10.98/1.78    inference(subsumption_resolution,[],[f2584,f481])).
% 10.98/1.78  fof(f2584,plain,(
% 10.98/1.78    ( ! [X4,X2,X3] : (~r1_tarski(k1_xboole_0,X4) | r1_tarski(k3_xboole_0(X2,X3),k2_xboole_0(X3,X4))) )),
% 10.98/1.78    inference(superposition,[],[f64,f640])).
% 10.98/1.78  fof(f640,plain,(
% 10.98/1.78    ( ! [X19,X18] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X18,X19),X19)) )),
% 10.98/1.78    inference(resolution,[],[f629,f58])).
% 10.98/1.78  fof(f29692,plain,(
% 10.98/1.78    ( ! [X4] : (r1_tarski(k2_xboole_0(X4,k1_xboole_0),X4)) )),
% 10.98/1.78    inference(superposition,[],[f29540,f61])).
% 10.98/1.78  fof(f29540,plain,(
% 10.98/1.78    ( ! [X41,X40] : (r1_tarski(k2_xboole_0(X41,k1_xboole_0),k2_xboole_0(X41,X40))) )),
% 10.98/1.78    inference(superposition,[],[f648,f321])).
% 10.98/1.78  fof(f648,plain,(
% 10.98/1.78    ( ! [X12,X10,X11] : (r1_tarski(k2_xboole_0(X10,k3_xboole_0(X11,X12)),k2_xboole_0(X10,X12))) )),
% 10.98/1.78    inference(superposition,[],[f629,f55])).
% 10.98/1.78  fof(f10567,plain,(
% 10.98/1.78    spl6_24),
% 10.98/1.78    inference(avatar_contradiction_clause,[],[f10566])).
% 10.98/1.78  fof(f10566,plain,(
% 10.98/1.78    $false | spl6_24),
% 10.98/1.78    inference(subsumption_resolution,[],[f10560,f1135])).
% 10.98/1.78  fof(f1135,plain,(
% 10.98/1.78    ~r1_tarski(sK2,sK2) | spl6_24),
% 10.98/1.78    inference(avatar_component_clause,[],[f1133])).
% 10.98/1.78  fof(f10560,plain,(
% 10.98/1.78    r1_tarski(sK2,sK2)),
% 10.98/1.78    inference(superposition,[],[f10508,f61])).
% 10.98/1.78  fof(f10508,plain,(
% 10.98/1.78    ( ! [X3] : (r1_tarski(sK2,k2_xboole_0(sK2,X3))) )),
% 10.98/1.78    inference(superposition,[],[f10489,f62])).
% 10.98/1.78  fof(f10489,plain,(
% 10.98/1.78    ( ! [X26,X27] : (r1_tarski(k4_xboole_0(sK2,X26),k2_xboole_0(sK2,X27))) )),
% 10.98/1.78    inference(resolution,[],[f10442,f67])).
% 10.98/1.78  fof(f10442,plain,(
% 10.98/1.78    ( ! [X0,X1] : (~r1_tarski(X0,sK2) | r1_tarski(X0,k2_xboole_0(sK2,X1))) )),
% 10.98/1.78    inference(subsumption_resolution,[],[f10430,f481])).
% 10.98/1.78  fof(f10430,plain,(
% 10.98/1.78    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,k3_xboole_0(X1,sK1)) | r1_tarski(X0,k2_xboole_0(sK2,X1)) | ~r1_tarski(X0,sK2)) )),
% 10.98/1.78    inference(superposition,[],[f718,f58])).
% 10.98/1.78  fof(f718,plain,(
% 10.98/1.78    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(X0,sK2),k3_xboole_0(X1,sK1)) | r1_tarski(X0,k2_xboole_0(sK2,X1))) )),
% 10.98/1.78    inference(resolution,[],[f226,f64])).
% 10.98/1.78  fof(f226,plain,(
% 10.98/1.78    ( ! [X15,X16] : (~r1_tarski(X16,k2_xboole_0(sK2,k3_xboole_0(X15,sK1))) | r1_tarski(X16,k2_xboole_0(sK2,X15))) )),
% 10.98/1.78    inference(superposition,[],[f66,f87])).
% 10.98/1.78  % SZS output end Proof for theBenchmark
% 10.98/1.78  % (26798)------------------------------
% 10.98/1.78  % (26798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.98/1.78  % (26798)Termination reason: Refutation
% 10.98/1.78  
% 10.98/1.78  % (26798)Memory used [KB]: 22899
% 10.98/1.78  % (26798)Time elapsed: 1.372 s
% 10.98/1.78  % (26798)------------------------------
% 10.98/1.78  % (26798)------------------------------
% 10.98/1.79  % (26775)Success in time 1.429 s
%------------------------------------------------------------------------------
