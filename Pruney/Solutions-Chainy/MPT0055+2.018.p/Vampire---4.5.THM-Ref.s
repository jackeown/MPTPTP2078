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
% DateTime   : Thu Dec  3 12:30:06 EST 2020

% Result     : Theorem 2.18s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 265 expanded)
%              Number of leaves         :   25 (  80 expanded)
%              Depth                    :   23
%              Number of atoms          :  346 (1188 expanded)
%              Number of equality atoms :   64 ( 187 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5941,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1296,f1388,f1693,f2501,f2693,f2699,f2913,f5940])).

fof(f5940,plain,
    ( ~ spl6_8
    | spl6_9
    | ~ spl6_22 ),
    inference(avatar_contradiction_clause,[],[f5939])).

fof(f5939,plain,
    ( $false
    | ~ spl6_8
    | spl6_9
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f5911,f169])).

fof(f169,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl6_9
  <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f5911,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl6_8
    | ~ spl6_22 ),
    inference(resolution,[],[f3486,f166])).

fof(f166,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl6_8
  <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f3486,plain,
    ( ! [X19,X20,X18] :
        ( ~ r2_hidden(X20,k3_xboole_0(X18,X19))
        | r2_hidden(X20,X18) )
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f3468,f637])).

fof(f637,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f636])).

fof(f636,plain,
    ( spl6_22
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f3468,plain,
    ( ! [X19,X20,X18] :
        ( r2_hidden(X20,k1_xboole_0)
        | r2_hidden(X20,X18)
        | ~ r2_hidden(X20,k3_xboole_0(X18,X19)) )
    | ~ spl6_22 ),
    inference(superposition,[],[f70,f3379])).

fof(f3379,plain,
    ( ! [X8,X7] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X7,X8),X7)
    | ~ spl6_22 ),
    inference(superposition,[],[f3141,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f3141,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))
    | ~ spl6_22 ),
    inference(superposition,[],[f977,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f977,plain,
    ( ! [X6,X7] : k1_xboole_0 = k4_xboole_0(X6,k2_xboole_0(X6,X7))
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f962,f760])).

fof(f760,plain,
    ( ! [X21] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X21)
    | ~ spl6_22 ),
    inference(resolution,[],[f700,f62])).

fof(f62,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f700,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(k1_xboole_0,X1))
    | ~ spl6_22 ),
    inference(resolution,[],[f637,f72])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f34,plain,(
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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f32])).

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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f962,plain,
    ( ! [X6,X7] : k4_xboole_0(k1_xboole_0,X7) = k4_xboole_0(X6,k2_xboole_0(X6,X7))
    | ~ spl6_22 ),
    inference(superposition,[],[f51,f926])).

fof(f926,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f924,f760])).

fof(f924,plain,
    ( ! [X2] : k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X2,X2)
    | ~ spl6_22 ),
    inference(superposition,[],[f56,f862])).

fof(f862,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl6_22 ),
    inference(resolution,[],[f846,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f846,plain,
    ( ! [X8] : r1_tarski(k1_xboole_0,X8)
    | ~ spl6_22 ),
    inference(trivial_inequality_removal,[],[f838])).

fof(f838,plain,
    ( ! [X8] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_tarski(k1_xboole_0,X8) )
    | ~ spl6_22 ),
    inference(superposition,[],[f52,f760])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2913,plain,
    ( spl6_8
    | spl6_9 ),
    inference(avatar_split_clause,[],[f2912,f168,f164])).

fof(f2912,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( k3_xboole_0(sK0,sK1) != X0
      | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X0),sK0)
      | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f43,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f43,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f29])).

fof(f29,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f2699,plain,
    ( ~ spl6_9
    | spl6_12
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f301,f164,f303,f168])).

fof(f303,plain,
    ( spl6_12
  <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f301,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f290,f43])).

fof(f290,plain,
    ( k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl6_8 ),
    inference(resolution,[],[f166,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2693,plain,
    ( ~ spl6_8
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f2692])).

fof(f2692,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f2682,f305])).

fof(f305,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f303])).

fof(f2682,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl6_8 ),
    inference(superposition,[],[f294,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f294,plain,
    ( ! [X2] : ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X2,k3_xboole_0(sK0,sK1)))
    | ~ spl6_8 ),
    inference(resolution,[],[f166,f71])).

fof(f71,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2501,plain,
    ( spl6_8
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f2500])).

fof(f2500,plain,
    ( $false
    | spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f2499,f1043])).

fof(f1043,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl6_8 ),
    inference(subsumption_resolution,[],[f1035,f43])).

fof(f1035,plain,
    ( k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl6_8 ),
    inference(resolution,[],[f165,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f165,plain,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f164])).

fof(f2499,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl6_8
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f2483,f57])).

fof(f2483,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | spl6_8
    | ~ spl6_9 ),
    inference(resolution,[],[f1037,f170])).

fof(f170,plain,
    ( r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f168])).

fof(f1037,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)
        | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1))) )
    | spl6_8 ),
    inference(resolution,[],[f165,f70])).

fof(f1693,plain,(
    spl6_20 ),
    inference(avatar_contradiction_clause,[],[f1692])).

fof(f1692,plain,
    ( $false
    | spl6_20 ),
    inference(subsumption_resolution,[],[f1683,f628])).

fof(f628,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK0)
    | spl6_20 ),
    inference(avatar_component_clause,[],[f627])).

fof(f627,plain,
    ( spl6_20
  <=> r1_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f1683,plain,
    ( r1_xboole_0(k1_xboole_0,sK0)
    | spl6_20 ),
    inference(resolution,[],[f678,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f678,plain,
    ( ! [X2] : ~ r2_hidden(sK5(k1_xboole_0,sK0),X2)
    | spl6_20 ),
    inference(forward_demodulation,[],[f675,f63])).

fof(f63,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f675,plain,
    ( ! [X2] : ~ r2_hidden(sK5(k1_xboole_0,sK0),k4_xboole_0(X2,k1_xboole_0))
    | spl6_20 ),
    inference(resolution,[],[f639,f71])).

fof(f639,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK0),k1_xboole_0)
    | spl6_20 ),
    inference(resolution,[],[f628,f67])).

fof(f1388,plain,
    ( ~ spl6_20
    | spl6_27 ),
    inference(avatar_contradiction_clause,[],[f1387])).

fof(f1387,plain,
    ( $false
    | ~ spl6_20
    | spl6_27 ),
    inference(subsumption_resolution,[],[f1328,f1297])).

fof(f1297,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK0)
    | spl6_27 ),
    inference(resolution,[],[f1295,f52])).

fof(f1295,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl6_27 ),
    inference(avatar_component_clause,[],[f1293])).

fof(f1293,plain,
    ( spl6_27
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f1328,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)
    | ~ spl6_20 ),
    inference(forward_demodulation,[],[f1324,f63])).

fof(f1324,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,sK0)
    | ~ spl6_20 ),
    inference(superposition,[],[f57,f1286])).

fof(f1286,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl6_20 ),
    inference(resolution,[],[f697,f62])).

fof(f697,plain,
    ( ! [X1] : ~ r2_hidden(X1,k3_xboole_0(k1_xboole_0,sK0))
    | ~ spl6_20 ),
    inference(resolution,[],[f629,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f629,plain,
    ( r1_xboole_0(k1_xboole_0,sK0)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f627])).

fof(f1296,plain,
    ( ~ spl6_27
    | spl6_22
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f1291,f627,f636,f1293])).

fof(f1291,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_xboole_0)
        | ~ r1_tarski(k1_xboole_0,sK0) )
    | ~ spl6_20 ),
    inference(superposition,[],[f697,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (15281)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (15299)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (15290)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (15290)Refutation not found, incomplete strategy% (15290)------------------------------
% 0.21/0.48  % (15290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (15290)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (15290)Memory used [KB]: 10618
% 0.21/0.48  % (15290)Time elapsed: 0.069 s
% 0.21/0.48  % (15290)------------------------------
% 0.21/0.48  % (15290)------------------------------
% 0.21/0.48  % (15280)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (15282)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (15284)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (15281)Refutation not found, incomplete strategy% (15281)------------------------------
% 0.21/0.48  % (15281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (15281)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.49  % (15281)Memory used [KB]: 10618
% 0.21/0.49  % (15281)Time elapsed: 0.071 s
% 0.21/0.49  % (15281)------------------------------
% 0.21/0.49  % (15281)------------------------------
% 0.21/0.49  % (15279)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (15279)Refutation not found, incomplete strategy% (15279)------------------------------
% 0.21/0.49  % (15279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (15279)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (15279)Memory used [KB]: 10618
% 0.21/0.49  % (15279)Time elapsed: 0.081 s
% 0.21/0.49  % (15279)------------------------------
% 0.21/0.49  % (15279)------------------------------
% 0.21/0.49  % (15292)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (15299)Refutation not found, incomplete strategy% (15299)------------------------------
% 0.21/0.49  % (15299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (15299)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (15299)Memory used [KB]: 10618
% 0.21/0.49  % (15299)Time elapsed: 0.089 s
% 0.21/0.49  % (15299)------------------------------
% 0.21/0.49  % (15299)------------------------------
% 0.21/0.49  % (15289)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (15289)Refutation not found, incomplete strategy% (15289)------------------------------
% 0.21/0.49  % (15289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (15289)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (15289)Memory used [KB]: 6012
% 0.21/0.49  % (15289)Time elapsed: 0.051 s
% 0.21/0.49  % (15289)------------------------------
% 0.21/0.49  % (15289)------------------------------
% 0.21/0.49  % (15286)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (15292)Refutation not found, incomplete strategy% (15292)------------------------------
% 0.21/0.49  % (15292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (15285)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (15278)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (15278)Refutation not found, incomplete strategy% (15278)------------------------------
% 0.21/0.49  % (15278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (15278)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (15278)Memory used [KB]: 6140
% 0.21/0.49  % (15278)Time elapsed: 0.083 s
% 0.21/0.49  % (15278)------------------------------
% 0.21/0.49  % (15278)------------------------------
% 0.21/0.50  % (15291)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (15293)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (15296)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (15288)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (15294)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (15294)Refutation not found, incomplete strategy% (15294)------------------------------
% 0.21/0.50  % (15294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (15294)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (15294)Memory used [KB]: 6140
% 0.21/0.50  % (15294)Time elapsed: 0.071 s
% 0.21/0.50  % (15294)------------------------------
% 0.21/0.50  % (15294)------------------------------
% 0.21/0.50  % (15298)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (15292)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (15292)Memory used [KB]: 1663
% 0.21/0.50  % (15292)Time elapsed: 0.088 s
% 0.21/0.50  % (15292)------------------------------
% 0.21/0.50  % (15292)------------------------------
% 0.21/0.51  % (15291)Refutation not found, incomplete strategy% (15291)------------------------------
% 0.21/0.51  % (15291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15291)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (15291)Memory used [KB]: 6012
% 0.21/0.51  % (15291)Time elapsed: 0.003 s
% 0.21/0.51  % (15291)------------------------------
% 0.21/0.51  % (15291)------------------------------
% 0.21/0.51  % (15297)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (15283)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (15295)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 2.18/0.63  % (15298)Refutation found. Thanks to Tanya!
% 2.18/0.63  % SZS status Theorem for theBenchmark
% 2.18/0.63  % SZS output start Proof for theBenchmark
% 2.18/0.63  fof(f5941,plain,(
% 2.18/0.63    $false),
% 2.18/0.63    inference(avatar_sat_refutation,[],[f1296,f1388,f1693,f2501,f2693,f2699,f2913,f5940])).
% 2.18/0.63  fof(f5940,plain,(
% 2.18/0.63    ~spl6_8 | spl6_9 | ~spl6_22),
% 2.18/0.63    inference(avatar_contradiction_clause,[],[f5939])).
% 2.18/0.63  fof(f5939,plain,(
% 2.18/0.63    $false | (~spl6_8 | spl6_9 | ~spl6_22)),
% 2.18/0.63    inference(subsumption_resolution,[],[f5911,f169])).
% 2.18/0.63  fof(f169,plain,(
% 2.18/0.63    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | spl6_9),
% 2.18/0.63    inference(avatar_component_clause,[],[f168])).
% 2.18/0.63  fof(f168,plain,(
% 2.18/0.63    spl6_9 <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 2.18/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 2.18/0.63  fof(f5911,plain,(
% 2.18/0.63    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | (~spl6_8 | ~spl6_22)),
% 2.18/0.63    inference(resolution,[],[f3486,f166])).
% 2.18/0.63  fof(f166,plain,(
% 2.18/0.63    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~spl6_8),
% 2.18/0.63    inference(avatar_component_clause,[],[f164])).
% 2.18/0.63  fof(f164,plain,(
% 2.18/0.63    spl6_8 <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.18/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.18/0.63  fof(f3486,plain,(
% 2.18/0.63    ( ! [X19,X20,X18] : (~r2_hidden(X20,k3_xboole_0(X18,X19)) | r2_hidden(X20,X18)) ) | ~spl6_22),
% 2.18/0.63    inference(subsumption_resolution,[],[f3468,f637])).
% 2.18/0.63  fof(f637,plain,(
% 2.18/0.63    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl6_22),
% 2.18/0.63    inference(avatar_component_clause,[],[f636])).
% 2.18/0.63  fof(f636,plain,(
% 2.18/0.63    spl6_22 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 2.18/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 2.18/0.63  fof(f3468,plain,(
% 2.18/0.63    ( ! [X19,X20,X18] : (r2_hidden(X20,k1_xboole_0) | r2_hidden(X20,X18) | ~r2_hidden(X20,k3_xboole_0(X18,X19))) ) | ~spl6_22),
% 2.18/0.63    inference(superposition,[],[f70,f3379])).
% 2.18/0.63  fof(f3379,plain,(
% 2.18/0.63    ( ! [X8,X7] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X7,X8),X7)) ) | ~spl6_22),
% 2.18/0.63    inference(superposition,[],[f3141,f58])).
% 2.18/0.63  fof(f58,plain,(
% 2.18/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.18/0.63    inference(cnf_transformation,[],[f11])).
% 2.18/0.63  fof(f11,axiom,(
% 2.18/0.63    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.18/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 2.18/0.63  fof(f3141,plain,(
% 2.18/0.63    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) ) | ~spl6_22),
% 2.18/0.63    inference(superposition,[],[f977,f60])).
% 2.18/0.63  fof(f60,plain,(
% 2.18/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.18/0.63    inference(cnf_transformation,[],[f1])).
% 2.18/0.63  fof(f1,axiom,(
% 2.18/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.18/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.18/0.63  fof(f977,plain,(
% 2.18/0.63    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(X6,k2_xboole_0(X6,X7))) ) | ~spl6_22),
% 2.18/0.63    inference(forward_demodulation,[],[f962,f760])).
% 2.18/0.63  fof(f760,plain,(
% 2.18/0.63    ( ! [X21] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X21)) ) | ~spl6_22),
% 2.18/0.63    inference(resolution,[],[f700,f62])).
% 2.18/0.63  fof(f62,plain,(
% 2.18/0.63    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.18/0.63    inference(cnf_transformation,[],[f38])).
% 2.18/0.63  fof(f38,plain,(
% 2.18/0.63    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 2.18/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f37])).
% 2.18/0.63  fof(f37,plain,(
% 2.18/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.18/0.63    introduced(choice_axiom,[])).
% 2.18/0.63  fof(f26,plain,(
% 2.18/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.18/0.63    inference(ennf_transformation,[],[f7])).
% 2.18/0.63  fof(f7,axiom,(
% 2.18/0.63    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.18/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.18/0.63  fof(f700,plain,(
% 2.18/0.63    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(k1_xboole_0,X1))) ) | ~spl6_22),
% 2.18/0.63    inference(resolution,[],[f637,f72])).
% 2.18/0.63  fof(f72,plain,(
% 2.18/0.63    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.18/0.63    inference(equality_resolution,[],[f44])).
% 2.18/0.63  fof(f44,plain,(
% 2.18/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.18/0.63    inference(cnf_transformation,[],[f35])).
% 2.18/0.63  fof(f35,plain,(
% 2.18/0.63    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.18/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 2.18/0.63  fof(f34,plain,(
% 2.18/0.63    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.18/0.63    introduced(choice_axiom,[])).
% 2.18/0.63  fof(f33,plain,(
% 2.18/0.63    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.18/0.63    inference(rectify,[],[f32])).
% 2.18/0.63  fof(f32,plain,(
% 2.18/0.63    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.18/0.63    inference(flattening,[],[f31])).
% 2.18/0.63  fof(f31,plain,(
% 2.18/0.63    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.18/0.63    inference(nnf_transformation,[],[f3])).
% 2.18/0.63  fof(f3,axiom,(
% 2.18/0.63    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.18/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.18/0.63  fof(f962,plain,(
% 2.18/0.63    ( ! [X6,X7] : (k4_xboole_0(k1_xboole_0,X7) = k4_xboole_0(X6,k2_xboole_0(X6,X7))) ) | ~spl6_22),
% 2.18/0.63    inference(superposition,[],[f51,f926])).
% 2.18/0.63  fof(f926,plain,(
% 2.18/0.63    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) ) | ~spl6_22),
% 2.18/0.63    inference(forward_demodulation,[],[f924,f760])).
% 2.18/0.63  fof(f924,plain,(
% 2.18/0.63    ( ! [X2] : (k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X2,X2)) ) | ~spl6_22),
% 2.18/0.63    inference(superposition,[],[f56,f862])).
% 2.18/0.63  fof(f862,plain,(
% 2.18/0.63    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl6_22),
% 2.18/0.63    inference(resolution,[],[f846,f55])).
% 2.18/0.63  fof(f55,plain,(
% 2.18/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.18/0.63    inference(cnf_transformation,[],[f25])).
% 2.18/0.63  fof(f25,plain,(
% 2.18/0.63    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.18/0.63    inference(ennf_transformation,[],[f9])).
% 2.18/0.63  fof(f9,axiom,(
% 2.18/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.18/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.18/0.63  fof(f846,plain,(
% 2.18/0.63    ( ! [X8] : (r1_tarski(k1_xboole_0,X8)) ) | ~spl6_22),
% 2.18/0.63    inference(trivial_inequality_removal,[],[f838])).
% 2.18/0.63  fof(f838,plain,(
% 2.18/0.63    ( ! [X8] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X8)) ) | ~spl6_22),
% 2.18/0.63    inference(superposition,[],[f52,f760])).
% 2.18/0.63  fof(f52,plain,(
% 2.18/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.18/0.63    inference(cnf_transformation,[],[f36])).
% 2.18/0.63  fof(f36,plain,(
% 2.18/0.63    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.18/0.63    inference(nnf_transformation,[],[f8])).
% 2.18/0.63  fof(f8,axiom,(
% 2.18/0.63    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.18/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.18/0.63  fof(f56,plain,(
% 2.18/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.18/0.63    inference(cnf_transformation,[],[f15])).
% 2.18/0.63  fof(f15,axiom,(
% 2.18/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.18/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.18/0.63  fof(f51,plain,(
% 2.18/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.18/0.63    inference(cnf_transformation,[],[f16])).
% 2.18/0.63  fof(f16,axiom,(
% 2.18/0.63    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.18/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.18/0.63  fof(f70,plain,(
% 2.18/0.63    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.18/0.63    inference(equality_resolution,[],[f46])).
% 2.18/0.63  fof(f46,plain,(
% 2.18/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.18/0.63    inference(cnf_transformation,[],[f35])).
% 2.18/0.63  fof(f2913,plain,(
% 2.18/0.63    spl6_8 | spl6_9),
% 2.18/0.63    inference(avatar_split_clause,[],[f2912,f168,f164])).
% 2.18/0.63  fof(f2912,plain,(
% 2.18/0.63    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.18/0.63    inference(equality_resolution,[],[f78])).
% 2.18/0.63  fof(f78,plain,(
% 2.18/0.63    ( ! [X0] : (k3_xboole_0(sK0,sK1) != X0 | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X0),sK0) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),X0),X0)) )),
% 2.18/0.63    inference(superposition,[],[f43,f47])).
% 2.18/0.63  fof(f47,plain,(
% 2.18/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.18/0.63    inference(cnf_transformation,[],[f35])).
% 2.18/0.63  fof(f43,plain,(
% 2.18/0.63    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.18/0.63    inference(cnf_transformation,[],[f30])).
% 2.18/0.63  fof(f30,plain,(
% 2.18/0.63    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.18/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f29])).
% 2.18/0.63  fof(f29,plain,(
% 2.18/0.63    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.18/0.63    introduced(choice_axiom,[])).
% 2.18/0.63  fof(f23,plain,(
% 2.18/0.63    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.18/0.63    inference(ennf_transformation,[],[f19])).
% 2.18/0.63  fof(f19,negated_conjecture,(
% 2.18/0.63    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.18/0.63    inference(negated_conjecture,[],[f18])).
% 2.18/0.63  fof(f18,conjecture,(
% 2.18/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.18/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.18/0.63  fof(f2699,plain,(
% 2.18/0.63    ~spl6_9 | spl6_12 | ~spl6_8),
% 2.18/0.63    inference(avatar_split_clause,[],[f301,f164,f303,f168])).
% 2.18/0.63  fof(f303,plain,(
% 2.18/0.63    spl6_12 <=> r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 2.18/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 2.18/0.63  fof(f301,plain,(
% 2.18/0.63    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~spl6_8),
% 2.18/0.63    inference(subsumption_resolution,[],[f290,f43])).
% 2.18/0.63  fof(f290,plain,(
% 2.18/0.63    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~spl6_8),
% 2.18/0.63    inference(resolution,[],[f166,f49])).
% 2.18/0.63  fof(f49,plain,(
% 2.18/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.18/0.63    inference(cnf_transformation,[],[f35])).
% 2.18/0.63  fof(f2693,plain,(
% 2.18/0.63    ~spl6_8 | ~spl6_12),
% 2.18/0.63    inference(avatar_contradiction_clause,[],[f2692])).
% 2.18/0.63  fof(f2692,plain,(
% 2.18/0.63    $false | (~spl6_8 | ~spl6_12)),
% 2.18/0.63    inference(subsumption_resolution,[],[f2682,f305])).
% 2.18/0.63  fof(f305,plain,(
% 2.18/0.63    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl6_12),
% 2.18/0.63    inference(avatar_component_clause,[],[f303])).
% 2.18/0.63  fof(f2682,plain,(
% 2.18/0.63    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl6_8),
% 2.18/0.63    inference(superposition,[],[f294,f57])).
% 2.18/0.63  fof(f57,plain,(
% 2.18/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.18/0.63    inference(cnf_transformation,[],[f17])).
% 2.18/0.63  fof(f17,axiom,(
% 2.18/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.18/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.18/0.63  fof(f294,plain,(
% 2.18/0.63    ( ! [X2] : (~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X2,k3_xboole_0(sK0,sK1)))) ) | ~spl6_8),
% 2.18/0.63    inference(resolution,[],[f166,f71])).
% 2.18/0.63  fof(f71,plain,(
% 2.18/0.63    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.18/0.63    inference(equality_resolution,[],[f45])).
% 2.18/0.63  fof(f45,plain,(
% 2.18/0.63    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.18/0.63    inference(cnf_transformation,[],[f35])).
% 2.18/0.63  fof(f2501,plain,(
% 2.18/0.63    spl6_8 | ~spl6_9),
% 2.18/0.63    inference(avatar_contradiction_clause,[],[f2500])).
% 2.18/0.63  fof(f2500,plain,(
% 2.18/0.63    $false | (spl6_8 | ~spl6_9)),
% 2.18/0.63    inference(subsumption_resolution,[],[f2499,f1043])).
% 2.18/0.63  fof(f1043,plain,(
% 2.18/0.63    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | spl6_8),
% 2.18/0.63    inference(subsumption_resolution,[],[f1035,f43])).
% 2.18/0.63  fof(f1035,plain,(
% 2.18/0.63    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | spl6_8),
% 2.18/0.63    inference(resolution,[],[f165,f48])).
% 2.18/0.63  fof(f48,plain,(
% 2.18/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.18/0.63    inference(cnf_transformation,[],[f35])).
% 2.18/0.63  fof(f165,plain,(
% 2.18/0.63    ~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | spl6_8),
% 2.18/0.63    inference(avatar_component_clause,[],[f164])).
% 2.18/0.63  fof(f2499,plain,(
% 2.18/0.63    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | (spl6_8 | ~spl6_9)),
% 2.18/0.63    inference(forward_demodulation,[],[f2483,f57])).
% 2.18/0.63  fof(f2483,plain,(
% 2.18/0.63    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))) | (spl6_8 | ~spl6_9)),
% 2.18/0.63    inference(resolution,[],[f1037,f170])).
% 2.18/0.63  fof(f170,plain,(
% 2.18/0.63    r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~spl6_9),
% 2.18/0.63    inference(avatar_component_clause,[],[f168])).
% 2.18/0.63  fof(f1037,plain,(
% 2.18/0.63    ( ! [X1] : (~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1)))) ) | spl6_8),
% 2.18/0.63    inference(resolution,[],[f165,f70])).
% 2.18/0.63  fof(f1693,plain,(
% 2.18/0.63    spl6_20),
% 2.18/0.63    inference(avatar_contradiction_clause,[],[f1692])).
% 2.18/0.63  fof(f1692,plain,(
% 2.18/0.63    $false | spl6_20),
% 2.18/0.63    inference(subsumption_resolution,[],[f1683,f628])).
% 2.18/0.63  fof(f628,plain,(
% 2.18/0.63    ~r1_xboole_0(k1_xboole_0,sK0) | spl6_20),
% 2.18/0.63    inference(avatar_component_clause,[],[f627])).
% 2.18/0.63  fof(f627,plain,(
% 2.18/0.63    spl6_20 <=> r1_xboole_0(k1_xboole_0,sK0)),
% 2.18/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 2.18/0.63  fof(f1683,plain,(
% 2.18/0.63    r1_xboole_0(k1_xboole_0,sK0) | spl6_20),
% 2.18/0.63    inference(resolution,[],[f678,f67])).
% 2.18/0.63  fof(f67,plain,(
% 2.18/0.63    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.18/0.63    inference(cnf_transformation,[],[f42])).
% 2.18/0.63  fof(f42,plain,(
% 2.18/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.18/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f41])).
% 2.18/0.63  fof(f41,plain,(
% 2.18/0.63    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 2.18/0.63    introduced(choice_axiom,[])).
% 2.18/0.63  fof(f28,plain,(
% 2.18/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.18/0.63    inference(ennf_transformation,[],[f22])).
% 2.18/0.63  fof(f22,plain,(
% 2.18/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.18/0.63    inference(rectify,[],[f5])).
% 2.18/0.63  fof(f5,axiom,(
% 2.18/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.18/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.18/0.63  fof(f678,plain,(
% 2.18/0.63    ( ! [X2] : (~r2_hidden(sK5(k1_xboole_0,sK0),X2)) ) | spl6_20),
% 2.18/0.63    inference(forward_demodulation,[],[f675,f63])).
% 2.18/0.63  fof(f63,plain,(
% 2.18/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.18/0.63    inference(cnf_transformation,[],[f14])).
% 2.18/0.63  fof(f14,axiom,(
% 2.18/0.63    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.18/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.18/0.63  fof(f675,plain,(
% 2.18/0.63    ( ! [X2] : (~r2_hidden(sK5(k1_xboole_0,sK0),k4_xboole_0(X2,k1_xboole_0))) ) | spl6_20),
% 2.18/0.63    inference(resolution,[],[f639,f71])).
% 2.18/0.63  fof(f639,plain,(
% 2.18/0.63    r2_hidden(sK5(k1_xboole_0,sK0),k1_xboole_0) | spl6_20),
% 2.18/0.63    inference(resolution,[],[f628,f67])).
% 2.18/0.63  fof(f1388,plain,(
% 2.18/0.63    ~spl6_20 | spl6_27),
% 2.18/0.63    inference(avatar_contradiction_clause,[],[f1387])).
% 2.18/0.63  fof(f1387,plain,(
% 2.18/0.63    $false | (~spl6_20 | spl6_27)),
% 2.18/0.63    inference(subsumption_resolution,[],[f1328,f1297])).
% 2.18/0.63  fof(f1297,plain,(
% 2.18/0.63    k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK0) | spl6_27),
% 2.18/0.63    inference(resolution,[],[f1295,f52])).
% 2.18/0.63  fof(f1295,plain,(
% 2.18/0.63    ~r1_tarski(k1_xboole_0,sK0) | spl6_27),
% 2.18/0.63    inference(avatar_component_clause,[],[f1293])).
% 2.18/0.63  fof(f1293,plain,(
% 2.18/0.63    spl6_27 <=> r1_tarski(k1_xboole_0,sK0)),
% 2.18/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 2.18/0.63  fof(f1328,plain,(
% 2.18/0.63    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) | ~spl6_20),
% 2.18/0.63    inference(forward_demodulation,[],[f1324,f63])).
% 2.18/0.63  fof(f1324,plain,(
% 2.18/0.63    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,sK0) | ~spl6_20),
% 2.18/0.63    inference(superposition,[],[f57,f1286])).
% 2.18/0.63  fof(f1286,plain,(
% 2.18/0.63    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0) | ~spl6_20),
% 2.18/0.63    inference(resolution,[],[f697,f62])).
% 2.18/0.63  fof(f697,plain,(
% 2.18/0.63    ( ! [X1] : (~r2_hidden(X1,k3_xboole_0(k1_xboole_0,sK0))) ) | ~spl6_20),
% 2.18/0.63    inference(resolution,[],[f629,f66])).
% 2.18/0.63  fof(f66,plain,(
% 2.18/0.63    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.18/0.63    inference(cnf_transformation,[],[f40])).
% 2.18/0.63  fof(f40,plain,(
% 2.18/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.18/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f39])).
% 2.18/0.63  fof(f39,plain,(
% 2.18/0.63    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 2.18/0.63    introduced(choice_axiom,[])).
% 2.18/0.63  fof(f27,plain,(
% 2.18/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.18/0.63    inference(ennf_transformation,[],[f21])).
% 2.18/0.63  fof(f21,plain,(
% 2.18/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.18/0.63    inference(rectify,[],[f6])).
% 2.18/0.63  fof(f6,axiom,(
% 2.18/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.18/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.18/0.63  fof(f629,plain,(
% 2.18/0.63    r1_xboole_0(k1_xboole_0,sK0) | ~spl6_20),
% 2.18/0.63    inference(avatar_component_clause,[],[f627])).
% 2.18/0.63  fof(f1296,plain,(
% 2.18/0.63    ~spl6_27 | spl6_22 | ~spl6_20),
% 2.18/0.63    inference(avatar_split_clause,[],[f1291,f627,f636,f1293])).
% 2.18/0.63  fof(f1291,plain,(
% 2.18/0.63    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0) | ~r1_tarski(k1_xboole_0,sK0)) ) | ~spl6_20),
% 2.18/0.63    inference(superposition,[],[f697,f54])).
% 2.18/0.63  fof(f54,plain,(
% 2.18/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.18/0.63    inference(cnf_transformation,[],[f24])).
% 2.18/0.63  fof(f24,plain,(
% 2.18/0.63    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.18/0.63    inference(ennf_transformation,[],[f12])).
% 2.18/0.63  fof(f12,axiom,(
% 2.18/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.18/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.18/0.63  % SZS output end Proof for theBenchmark
% 2.18/0.63  % (15298)------------------------------
% 2.18/0.63  % (15298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.63  % (15298)Termination reason: Refutation
% 2.18/0.63  
% 2.18/0.63  % (15298)Memory used [KB]: 8059
% 2.18/0.63  % (15298)Time elapsed: 0.225 s
% 2.18/0.63  % (15298)------------------------------
% 2.18/0.63  % (15298)------------------------------
% 2.18/0.64  % (15272)Success in time 0.277 s
%------------------------------------------------------------------------------
