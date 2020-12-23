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
% DateTime   : Thu Dec  3 12:35:26 EST 2020

% Result     : Theorem 2.02s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   96 (1174 expanded)
%              Number of leaves         :   17 ( 301 expanded)
%              Depth                    :   28
%              Number of atoms          :  236 (5084 expanded)
%              Number of equality atoms :   73 ( 605 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1260,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1256,f41])).

fof(f41,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK1 != sK2
    & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK1 != sK2
      & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f1256,plain,(
    sK1 = sK2 ),
    inference(resolution,[],[f1255,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f1255,plain,(
    r1_tarski(k1_tarski(sK2),k1_tarski(sK1)) ),
    inference(superposition,[],[f1201,f1042])).

fof(f1042,plain,(
    k1_tarski(sK2) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(superposition,[],[f944,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f944,plain,(
    k1_tarski(sK2) = k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f925,f43])).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f925,plain,(
    k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK2),k1_xboole_0) ),
    inference(superposition,[],[f519,f731])).

fof(f731,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f713,f337])).

fof(f337,plain,(
    ! [X7] : k1_xboole_0 = k4_xboole_0(X7,X7) ),
    inference(resolution,[],[f328,f115])).

fof(f115,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f55,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f328,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(resolution,[],[f297,f72])).

fof(f72,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f297,plain,(
    ! [X19,X17,X18,X16] :
      ( ~ sP0(X16,X19,k4_xboole_0(X16,X17))
      | r1_tarski(k4_xboole_0(X16,X17),X18) ) ),
    inference(duplicate_literal_removal,[],[f293])).

fof(f293,plain,(
    ! [X19,X17,X18,X16] :
      ( r1_tarski(k4_xboole_0(X16,X17),X18)
      | ~ sP0(X16,X19,k4_xboole_0(X16,X17))
      | r1_tarski(k4_xboole_0(X16,X17),X18) ) ),
    inference(resolution,[],[f274,f149])).

fof(f149,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X2)
      | ~ sP0(X2,X3,X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f62,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
              & r2_hidden(sK4(X0,X1,X2),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            & r2_hidden(sK4(X0,X1,X2),X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f274,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(k4_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f148,f72])).

fof(f148,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X3,X2,X0)
      | r2_hidden(sK3(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f61,f57])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f713,plain,(
    k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) = k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)) ),
    inference(superposition,[],[f677,f40])).

fof(f40,plain,(
    k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f677,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),X6) = k4_xboole_0(X7,X6) ),
    inference(backward_demodulation,[],[f128,f662])).

fof(f662,plain,(
    ! [X6,X5] : k4_xboole_0(X6,X5) = k5_xboole_0(k2_xboole_0(X5,X6),X5) ),
    inference(superposition,[],[f619,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f619,plain,(
    ! [X10,X9] : k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9 ),
    inference(superposition,[],[f607,f607])).

fof(f607,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f595,f43])).

fof(f595,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f515,f357])).

fof(f357,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(backward_demodulation,[],[f160,f337])).

fof(f160,plain,(
    ! [X4,X3] : k4_xboole_0(k5_xboole_0(X3,X4),k5_xboole_0(X3,X4)) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f60,f89])).

fof(f89,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f48,f75])).

fof(f75,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(resolution,[],[f51,f70])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f60,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f515,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f348,f512])).

fof(f512,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f498,f43])).

fof(f498,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f348,f343])).

fof(f343,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f89,f337])).

fof(f348,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f154,f337])).

fof(f154,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[],[f60,f89])).

fof(f128,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),X6) = k5_xboole_0(k2_xboole_0(X6,X7),X6) ),
    inference(superposition,[],[f90,f76])).

fof(f76,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2 ),
    inference(resolution,[],[f51,f45])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f90,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f48,f46])).

fof(f519,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f499,f512])).

fof(f499,plain,(
    ! [X2,X1] : k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f348,f48])).

fof(f1201,plain,(
    ! [X14,X15] : r1_tarski(k3_xboole_0(X14,X15),X14) ),
    inference(superposition,[],[f298,f520])).

fof(f520,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f312,f519])).

fof(f312,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f90,f301])).

fof(f301,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k3_xboole_0(k4_xboole_0(X5,X6),X5) ),
    inference(resolution,[],[f298,f51])).

fof(f298,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(duplicate_literal_removal,[],[f289])).

fof(f289,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X0)
      | r1_tarski(k4_xboole_0(X0,X1),X0) ) ),
    inference(resolution,[],[f274,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:32:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (22151)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.49  % (22143)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (22145)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (22145)Refutation not found, incomplete strategy% (22145)------------------------------
% 0.21/0.50  % (22145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (22145)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (22145)Memory used [KB]: 10618
% 0.21/0.50  % (22145)Time elapsed: 0.094 s
% 0.21/0.50  % (22145)------------------------------
% 0.21/0.50  % (22145)------------------------------
% 0.21/0.51  % (22161)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (22139)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (22153)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.25/0.52  % (22148)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.25/0.52  % (22155)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.25/0.52  % (22149)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.25/0.53  % (22147)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.53  % (22135)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.25/0.53  % (22141)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.25/0.53  % (22163)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.25/0.53  % (22136)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.25/0.53  % (22138)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.38/0.53  % (22157)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.38/0.54  % (22158)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.54  % (22140)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.38/0.54  % (22158)Refutation not found, incomplete strategy% (22158)------------------------------
% 1.38/0.54  % (22158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (22158)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (22158)Memory used [KB]: 1663
% 1.38/0.54  % (22158)Time elapsed: 0.112 s
% 1.38/0.54  % (22158)------------------------------
% 1.38/0.54  % (22158)------------------------------
% 1.38/0.54  % (22162)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.54  % (22155)Refutation not found, incomplete strategy% (22155)------------------------------
% 1.38/0.54  % (22155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (22155)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (22155)Memory used [KB]: 10746
% 1.38/0.54  % (22155)Time elapsed: 0.142 s
% 1.38/0.54  % (22155)------------------------------
% 1.38/0.54  % (22155)------------------------------
% 1.38/0.54  % (22137)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.38/0.55  % (22159)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.55  % (22154)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.55  % (22164)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.55  % (22146)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.38/0.55  % (22146)Refutation not found, incomplete strategy% (22146)------------------------------
% 1.38/0.55  % (22146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (22146)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (22146)Memory used [KB]: 10618
% 1.38/0.55  % (22146)Time elapsed: 0.148 s
% 1.38/0.55  % (22146)------------------------------
% 1.38/0.55  % (22146)------------------------------
% 1.38/0.56  % (22156)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.56  % (22150)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.56  % (22142)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.56  % (22160)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.57  % (22152)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.38/0.57  % (22152)Refutation not found, incomplete strategy% (22152)------------------------------
% 1.38/0.57  % (22152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (22152)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.57  
% 1.38/0.57  % (22152)Memory used [KB]: 10618
% 1.38/0.57  % (22152)Time elapsed: 0.169 s
% 1.38/0.57  % (22152)------------------------------
% 1.38/0.57  % (22152)------------------------------
% 1.38/0.58  % (22144)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.38/0.62  % (22165)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.02/0.64  % (22142)Refutation found. Thanks to Tanya!
% 2.02/0.64  % SZS status Theorem for theBenchmark
% 2.02/0.64  % SZS output start Proof for theBenchmark
% 2.02/0.64  fof(f1260,plain,(
% 2.02/0.64    $false),
% 2.02/0.64    inference(subsumption_resolution,[],[f1256,f41])).
% 2.02/0.64  fof(f41,plain,(
% 2.02/0.64    sK1 != sK2),
% 2.02/0.64    inference(cnf_transformation,[],[f27])).
% 2.02/0.64  fof(f27,plain,(
% 2.02/0.64    sK1 != sK2 & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 2.02/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f26])).
% 2.02/0.64  fof(f26,plain,(
% 2.02/0.64    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK1 != sK2 & k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 2.02/0.64    introduced(choice_axiom,[])).
% 2.02/0.64  fof(f20,plain,(
% 2.02/0.64    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 2.02/0.64    inference(ennf_transformation,[],[f19])).
% 2.02/0.64  fof(f19,negated_conjecture,(
% 2.02/0.64    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.02/0.64    inference(negated_conjecture,[],[f18])).
% 2.02/0.64  fof(f18,conjecture,(
% 2.02/0.64    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 2.02/0.64  fof(f1256,plain,(
% 2.02/0.64    sK1 = sK2),
% 2.02/0.64    inference(resolution,[],[f1255,f52])).
% 2.02/0.64  fof(f52,plain,(
% 2.02/0.64    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 2.02/0.64    inference(cnf_transformation,[],[f22])).
% 2.02/0.64  fof(f22,plain,(
% 2.02/0.64    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 2.02/0.64    inference(ennf_transformation,[],[f17])).
% 2.02/0.64  fof(f17,axiom,(
% 2.02/0.64    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 2.02/0.64  fof(f1255,plain,(
% 2.02/0.64    r1_tarski(k1_tarski(sK2),k1_tarski(sK1))),
% 2.02/0.64    inference(superposition,[],[f1201,f1042])).
% 2.02/0.64  fof(f1042,plain,(
% 2.02/0.64    k1_tarski(sK2) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 2.02/0.64    inference(superposition,[],[f944,f46])).
% 2.02/0.64  fof(f46,plain,(
% 2.02/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f1])).
% 2.02/0.64  fof(f1,axiom,(
% 2.02/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.02/0.64  fof(f944,plain,(
% 2.02/0.64    k1_tarski(sK2) = k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),
% 2.02/0.64    inference(forward_demodulation,[],[f925,f43])).
% 2.02/0.64  fof(f43,plain,(
% 2.02/0.64    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.02/0.64    inference(cnf_transformation,[],[f9])).
% 2.02/0.64  fof(f9,axiom,(
% 2.02/0.64    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.02/0.64  fof(f925,plain,(
% 2.02/0.64    k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK2),k1_xboole_0)),
% 2.02/0.64    inference(superposition,[],[f519,f731])).
% 2.02/0.64  fof(f731,plain,(
% 2.02/0.64    k1_xboole_0 = k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),
% 2.02/0.64    inference(forward_demodulation,[],[f713,f337])).
% 2.02/0.64  fof(f337,plain,(
% 2.02/0.64    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(X7,X7)) )),
% 2.02/0.64    inference(resolution,[],[f328,f115])).
% 2.02/0.64  fof(f115,plain,(
% 2.02/0.64    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.02/0.64    inference(resolution,[],[f55,f42])).
% 2.02/0.64  fof(f42,plain,(
% 2.02/0.64    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f7])).
% 2.02/0.64  fof(f7,axiom,(
% 2.02/0.64    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.02/0.64  fof(f55,plain,(
% 2.02/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.02/0.64    inference(cnf_transformation,[],[f29])).
% 2.02/0.64  fof(f29,plain,(
% 2.02/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.02/0.64    inference(flattening,[],[f28])).
% 2.02/0.64  fof(f28,plain,(
% 2.02/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.02/0.64    inference(nnf_transformation,[],[f4])).
% 2.02/0.64  fof(f4,axiom,(
% 2.02/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.02/0.64  fof(f328,plain,(
% 2.02/0.64    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 2.02/0.64    inference(resolution,[],[f297,f72])).
% 2.02/0.64  fof(f72,plain,(
% 2.02/0.64    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 2.02/0.64    inference(equality_resolution,[],[f67])).
% 2.02/0.64  fof(f67,plain,(
% 2.02/0.64    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.02/0.64    inference(cnf_transformation,[],[f39])).
% 2.02/0.64  fof(f39,plain,(
% 2.02/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 2.02/0.64    inference(nnf_transformation,[],[f25])).
% 2.02/0.64  fof(f25,plain,(
% 2.02/0.64    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 2.02/0.64    inference(definition_folding,[],[f3,f24])).
% 2.02/0.64  fof(f24,plain,(
% 2.02/0.64    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.02/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.02/0.64  fof(f3,axiom,(
% 2.02/0.64    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.02/0.64  fof(f297,plain,(
% 2.02/0.64    ( ! [X19,X17,X18,X16] : (~sP0(X16,X19,k4_xboole_0(X16,X17)) | r1_tarski(k4_xboole_0(X16,X17),X18)) )),
% 2.02/0.64    inference(duplicate_literal_removal,[],[f293])).
% 2.02/0.64  fof(f293,plain,(
% 2.02/0.64    ( ! [X19,X17,X18,X16] : (r1_tarski(k4_xboole_0(X16,X17),X18) | ~sP0(X16,X19,k4_xboole_0(X16,X17)) | r1_tarski(k4_xboole_0(X16,X17),X18)) )),
% 2.02/0.64    inference(resolution,[],[f274,f149])).
% 2.02/0.64  fof(f149,plain,(
% 2.02/0.64    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK3(X0,X1),X2) | ~sP0(X2,X3,X0) | r1_tarski(X0,X1)) )),
% 2.02/0.64    inference(resolution,[],[f62,f57])).
% 2.02/0.64  fof(f57,plain,(
% 2.02/0.64    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f33])).
% 2.02/0.64  fof(f33,plain,(
% 2.02/0.64    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.02/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 2.02/0.64  fof(f32,plain,(
% 2.02/0.64    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 2.02/0.64    introduced(choice_axiom,[])).
% 2.02/0.64  fof(f31,plain,(
% 2.02/0.64    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.02/0.64    inference(rectify,[],[f30])).
% 2.02/0.64  fof(f30,plain,(
% 2.02/0.64    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.02/0.64    inference(nnf_transformation,[],[f23])).
% 2.02/0.64  fof(f23,plain,(
% 2.02/0.64    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.02/0.64    inference(ennf_transformation,[],[f2])).
% 2.02/0.64  fof(f2,axiom,(
% 2.02/0.64    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.02/0.64  fof(f62,plain,(
% 2.02/0.64    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~sP0(X0,X1,X2)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f38])).
% 2.02/0.64  fof(f38,plain,(
% 2.02/0.64    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 2.02/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 2.02/0.64  fof(f37,plain,(
% 2.02/0.64    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.02/0.64    introduced(choice_axiom,[])).
% 2.02/0.64  fof(f36,plain,(
% 2.02/0.64    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 2.02/0.64    inference(rectify,[],[f35])).
% 2.02/0.64  fof(f35,plain,(
% 2.02/0.64    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 2.02/0.64    inference(flattening,[],[f34])).
% 2.02/0.64  fof(f34,plain,(
% 2.02/0.64    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 2.02/0.64    inference(nnf_transformation,[],[f24])).
% 2.02/0.64  fof(f274,plain,(
% 2.02/0.64    ( ! [X2,X0,X1] : (r2_hidden(sK3(k4_xboole_0(X0,X1),X2),X0) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.02/0.64    inference(resolution,[],[f148,f72])).
% 2.02/0.64  fof(f148,plain,(
% 2.02/0.64    ( ! [X2,X0,X3,X1] : (~sP0(X3,X2,X0) | r2_hidden(sK3(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 2.02/0.64    inference(resolution,[],[f61,f57])).
% 2.02/0.64  fof(f61,plain,(
% 2.02/0.64    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~sP0(X0,X1,X2)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f38])).
% 2.02/0.64  fof(f713,plain,(
% 2.02/0.64    k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) = k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),
% 2.02/0.64    inference(superposition,[],[f677,f40])).
% 2.02/0.64  fof(f40,plain,(
% 2.02/0.64    k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 2.02/0.64    inference(cnf_transformation,[],[f27])).
% 2.02/0.64  fof(f677,plain,(
% 2.02/0.64    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),X6) = k4_xboole_0(X7,X6)) )),
% 2.02/0.64    inference(backward_demodulation,[],[f128,f662])).
% 2.02/0.64  fof(f662,plain,(
% 2.02/0.64    ( ! [X6,X5] : (k4_xboole_0(X6,X5) = k5_xboole_0(k2_xboole_0(X5,X6),X5)) )),
% 2.02/0.64    inference(superposition,[],[f619,f49])).
% 2.02/0.64  fof(f49,plain,(
% 2.02/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.02/0.64    inference(cnf_transformation,[],[f12])).
% 2.02/0.64  fof(f12,axiom,(
% 2.02/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.02/0.64  fof(f619,plain,(
% 2.02/0.64    ( ! [X10,X9] : (k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9) )),
% 2.02/0.64    inference(superposition,[],[f607,f607])).
% 2.02/0.64  fof(f607,plain,(
% 2.02/0.64    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 2.02/0.64    inference(forward_demodulation,[],[f595,f43])).
% 2.02/0.64  fof(f595,plain,(
% 2.02/0.64    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k1_xboole_0)) )),
% 2.02/0.64    inference(superposition,[],[f515,f357])).
% 2.02/0.64  fof(f357,plain,(
% 2.02/0.64    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 2.02/0.64    inference(backward_demodulation,[],[f160,f337])).
% 2.02/0.64  fof(f160,plain,(
% 2.02/0.64    ( ! [X4,X3] : (k4_xboole_0(k5_xboole_0(X3,X4),k5_xboole_0(X3,X4)) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 2.02/0.64    inference(superposition,[],[f60,f89])).
% 2.02/0.64  fof(f89,plain,(
% 2.02/0.64    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 2.02/0.64    inference(superposition,[],[f48,f75])).
% 2.02/0.64  fof(f75,plain,(
% 2.02/0.64    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 2.02/0.64    inference(resolution,[],[f51,f70])).
% 2.02/0.64  fof(f70,plain,(
% 2.02/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.02/0.64    inference(equality_resolution,[],[f54])).
% 2.02/0.64  fof(f54,plain,(
% 2.02/0.64    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.02/0.64    inference(cnf_transformation,[],[f29])).
% 2.02/0.64  fof(f51,plain,(
% 2.02/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.02/0.64    inference(cnf_transformation,[],[f21])).
% 2.02/0.64  fof(f21,plain,(
% 2.02/0.64    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.02/0.64    inference(ennf_transformation,[],[f6])).
% 2.02/0.64  fof(f6,axiom,(
% 2.02/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.02/0.64  fof(f48,plain,(
% 2.02/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.02/0.64    inference(cnf_transformation,[],[f5])).
% 2.02/0.64  fof(f5,axiom,(
% 2.02/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.02/0.64  fof(f60,plain,(
% 2.02/0.64    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.02/0.64    inference(cnf_transformation,[],[f11])).
% 2.02/0.64  fof(f11,axiom,(
% 2.02/0.64    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.02/0.64  fof(f515,plain,(
% 2.02/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.02/0.64    inference(backward_demodulation,[],[f348,f512])).
% 2.02/0.64  fof(f512,plain,(
% 2.02/0.64    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.02/0.64    inference(forward_demodulation,[],[f498,f43])).
% 2.02/0.64  fof(f498,plain,(
% 2.02/0.64    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 2.02/0.64    inference(superposition,[],[f348,f343])).
% 2.02/0.64  fof(f343,plain,(
% 2.02/0.64    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.02/0.64    inference(backward_demodulation,[],[f89,f337])).
% 2.02/0.64  fof(f348,plain,(
% 2.02/0.64    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.02/0.64    inference(backward_demodulation,[],[f154,f337])).
% 2.02/0.64  fof(f154,plain,(
% 2.02/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k4_xboole_0(X0,X0),X1)) )),
% 2.02/0.64    inference(superposition,[],[f60,f89])).
% 2.02/0.64  fof(f128,plain,(
% 2.02/0.64    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),X6) = k5_xboole_0(k2_xboole_0(X6,X7),X6)) )),
% 2.02/0.64    inference(superposition,[],[f90,f76])).
% 2.02/0.64  fof(f76,plain,(
% 2.02/0.64    ( ! [X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2) )),
% 2.02/0.64    inference(resolution,[],[f51,f45])).
% 2.02/0.64  fof(f45,plain,(
% 2.02/0.64    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.02/0.64    inference(cnf_transformation,[],[f10])).
% 2.02/0.64  fof(f10,axiom,(
% 2.02/0.64    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.02/0.64  fof(f90,plain,(
% 2.02/0.64    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 2.02/0.64    inference(superposition,[],[f48,f46])).
% 2.02/0.64  fof(f519,plain,(
% 2.02/0.64    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 2.02/0.64    inference(forward_demodulation,[],[f499,f512])).
% 2.02/0.64  fof(f499,plain,(
% 2.02/0.64    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 2.02/0.64    inference(superposition,[],[f348,f48])).
% 2.02/0.64  fof(f1201,plain,(
% 2.02/0.64    ( ! [X14,X15] : (r1_tarski(k3_xboole_0(X14,X15),X14)) )),
% 2.02/0.64    inference(superposition,[],[f298,f520])).
% 2.02/0.64  fof(f520,plain,(
% 2.02/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.02/0.64    inference(backward_demodulation,[],[f312,f519])).
% 2.02/0.64  fof(f312,plain,(
% 2.02/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.02/0.64    inference(superposition,[],[f90,f301])).
% 2.02/0.64  fof(f301,plain,(
% 2.02/0.64    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k3_xboole_0(k4_xboole_0(X5,X6),X5)) )),
% 2.02/0.64    inference(resolution,[],[f298,f51])).
% 2.02/0.64  fof(f298,plain,(
% 2.02/0.64    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.02/0.64    inference(duplicate_literal_removal,[],[f289])).
% 2.02/0.64  fof(f289,plain,(
% 2.02/0.64    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0) | r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.02/0.64    inference(resolution,[],[f274,f58])).
% 2.02/0.64  fof(f58,plain,(
% 2.02/0.64    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.02/0.64    inference(cnf_transformation,[],[f33])).
% 2.02/0.64  % SZS output end Proof for theBenchmark
% 2.02/0.64  % (22142)------------------------------
% 2.02/0.64  % (22142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.64  % (22142)Termination reason: Refutation
% 2.02/0.64  
% 2.02/0.64  % (22142)Memory used [KB]: 7036
% 2.02/0.64  % (22142)Time elapsed: 0.225 s
% 2.02/0.64  % (22142)------------------------------
% 2.02/0.64  % (22142)------------------------------
% 2.02/0.64  % (22134)Success in time 0.284 s
%------------------------------------------------------------------------------
