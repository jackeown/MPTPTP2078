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
% DateTime   : Thu Dec  3 12:39:06 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 326 expanded)
%              Number of leaves         :   17 (  93 expanded)
%              Depth                    :   20
%              Number of atoms          :  243 ( 834 expanded)
%              Number of equality atoms :   66 ( 256 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f488,plain,(
    $false ),
    inference(subsumption_resolution,[],[f487,f129])).

fof(f129,plain,(
    sK3 != k2_xboole_0(sK3,k2_tarski(sK2,sK4)) ),
    inference(superposition,[],[f50,f124])).

fof(f124,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f94,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f94,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f55,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f50,plain,(
    sK3 != k2_xboole_0(k2_tarski(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK3 != k2_xboole_0(k2_tarski(sK2,sK4),sK3)
    & r2_hidden(sK4,sK3)
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( sK3 != k2_xboole_0(k2_tarski(sK2,sK4),sK3)
      & r2_hidden(sK4,sK3)
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f487,plain,(
    sK3 = k2_xboole_0(sK3,k2_tarski(sK2,sK4)) ),
    inference(forward_demodulation,[],[f485,f52])).

fof(f52,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f485,plain,(
    k2_xboole_0(sK3,k2_tarski(sK2,sK4)) = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f58,f449])).

fof(f449,plain,(
    k1_xboole_0 = k4_xboole_0(k2_tarski(sK2,sK4),sK3) ),
    inference(backward_demodulation,[],[f283,f447])).

fof(f447,plain,(
    ! [X4] : k1_xboole_0 = k5_xboole_0(X4,X4) ),
    inference(backward_demodulation,[],[f138,f446])).

fof(f446,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(duplicate_literal_removal,[],[f435])).

fof(f435,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(X0,X0)
      | k1_xboole_0 = k4_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f349,f348])).

fof(f348,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(sK5(k4_xboole_0(X8,X9),k1_xboole_0),X9)
      | k1_xboole_0 = k4_xboole_0(X8,X9) ) ),
    inference(resolution,[],[f333,f208])).

fof(f208,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f67,f88])).

fof(f88,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f23])).

fof(f23,plain,(
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

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
              & r2_hidden(sK6(X0,X1,X2),X1) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
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
    inference(nnf_transformation,[],[f23])).

fof(f333,plain,(
    ! [X17] :
      ( r2_hidden(sK5(X17,k1_xboole_0),X17)
      | k1_xboole_0 = X17 ) ),
    inference(resolution,[],[f60,f212])).

fof(f212,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f209])).

fof(f209,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f67,f177])).

fof(f177,plain,(
    ! [X3] : sP0(X3,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f155,f175])).

fof(f175,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6) ),
    inference(backward_demodulation,[],[f140,f174])).

fof(f174,plain,(
    ! [X5] : k5_xboole_0(X5,k1_xboole_0) = X5 ),
    inference(backward_demodulation,[],[f139,f173])).

fof(f173,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(forward_demodulation,[],[f167,f126])).

fof(f126,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f124,f52])).

fof(f167,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f58,f126])).

fof(f139,plain,(
    ! [X5] : k4_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X5,k1_xboole_0) ),
    inference(superposition,[],[f57,f98])).

fof(f98,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f96,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f59,f51])).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f140,plain,(
    ! [X6] : k4_xboole_0(k1_xboole_0,X6) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f57,f96])).

fof(f155,plain,(
    ! [X2,X3] : sP0(X3,k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f145,f141])).

fof(f141,plain,(
    ! [X0,X1] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f140,f140])).

fof(f145,plain,(
    ! [X0] : sP0(X0,k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f143,f138])).

fof(f143,plain,(
    ! [X0] : sP0(X0,k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f88,f140])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r2_hidden(sK5(X0,X1),X0) )
        & ( r2_hidden(sK5(X0,X1),X1)
          | r2_hidden(sK5(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r2_hidden(sK5(X0,X1),X0) )
        & ( r2_hidden(sK5(X0,X1),X1)
          | r2_hidden(sK5(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f349,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK5(k4_xboole_0(X10,X11),k1_xboole_0),X10)
      | k1_xboole_0 = k4_xboole_0(X10,X11) ) ),
    inference(resolution,[],[f333,f203])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f66,f88])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f138,plain,(
    ! [X4] : k4_xboole_0(X4,X4) = k5_xboole_0(X4,X4) ),
    inference(superposition,[],[f57,f97])).

fof(f97,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(resolution,[],[f59,f86])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f283,plain,(
    k4_xboole_0(k2_tarski(sK2,sK4),sK3) = k5_xboole_0(k2_tarski(sK2,sK4),k2_tarski(sK2,sK4)) ),
    inference(superposition,[],[f57,f254])).

fof(f254,plain,(
    k2_tarski(sK2,sK4) = k3_xboole_0(k2_tarski(sK2,sK4),sK3) ),
    inference(resolution,[],[f246,f59])).

fof(f246,plain,(
    r1_tarski(k2_tarski(sK2,sK4),sK3) ),
    inference(resolution,[],[f241,f49])).

fof(f49,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f241,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r1_tarski(k2_tarski(sK2,X0),sK3) ) ),
    inference(resolution,[],[f84,f48])).

fof(f48,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (20085)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (20094)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (20085)Refutation not found, incomplete strategy% (20085)------------------------------
% 0.20/0.52  % (20085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (20085)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (20085)Memory used [KB]: 1663
% 0.20/0.52  % (20085)Time elapsed: 0.107 s
% 0.20/0.52  % (20085)------------------------------
% 0.20/0.52  % (20085)------------------------------
% 0.20/0.52  % (20094)Refutation not found, incomplete strategy% (20094)------------------------------
% 0.20/0.52  % (20094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (20094)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (20094)Memory used [KB]: 10618
% 0.20/0.52  % (20094)Time elapsed: 0.109 s
% 0.20/0.52  % (20094)------------------------------
% 0.20/0.52  % (20094)------------------------------
% 0.20/0.52  % (20099)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (20111)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (20105)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (20103)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (20087)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.56  % (20095)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.53/0.56  % (20092)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.53/0.56  % (20102)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.53/0.57  % (20086)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.53/0.57  % (20116)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.53/0.57  % (20110)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.53/0.57  % (20088)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.69/0.57  % (20109)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.69/0.57  % (20087)Refutation not found, incomplete strategy% (20087)------------------------------
% 1.69/0.57  % (20087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.57  % (20087)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.57  
% 1.69/0.57  % (20087)Memory used [KB]: 10618
% 1.69/0.57  % (20087)Time elapsed: 0.149 s
% 1.69/0.57  % (20087)------------------------------
% 1.69/0.57  % (20087)------------------------------
% 1.69/0.57  % (20090)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.69/0.58  % (20109)Refutation not found, incomplete strategy% (20109)------------------------------
% 1.69/0.58  % (20109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.58  % (20109)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.58  
% 1.69/0.58  % (20109)Memory used [KB]: 10746
% 1.69/0.58  % (20109)Time elapsed: 0.178 s
% 1.69/0.58  % (20109)------------------------------
% 1.69/0.58  % (20109)------------------------------
% 1.69/0.58  % (20095)Refutation not found, incomplete strategy% (20095)------------------------------
% 1.69/0.58  % (20095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.58  % (20095)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.58  
% 1.69/0.58  % (20095)Memory used [KB]: 10618
% 1.69/0.58  % (20095)Time elapsed: 0.177 s
% 1.69/0.58  % (20095)------------------------------
% 1.69/0.58  % (20095)------------------------------
% 1.69/0.58  % (20112)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.69/0.58  % (20101)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.69/0.59  % (20104)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.69/0.59  % (20104)Refutation not found, incomplete strategy% (20104)------------------------------
% 1.69/0.59  % (20104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.59  % (20104)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.59  
% 1.69/0.59  % (20104)Memory used [KB]: 10618
% 1.69/0.59  % (20104)Time elapsed: 0.161 s
% 1.69/0.59  % (20104)------------------------------
% 1.69/0.59  % (20104)------------------------------
% 1.69/0.60  % (20092)Refutation found. Thanks to Tanya!
% 1.69/0.60  % SZS status Theorem for theBenchmark
% 1.69/0.60  % SZS output start Proof for theBenchmark
% 1.69/0.60  fof(f488,plain,(
% 1.69/0.60    $false),
% 1.69/0.60    inference(subsumption_resolution,[],[f487,f129])).
% 1.69/0.60  fof(f129,plain,(
% 1.69/0.60    sK3 != k2_xboole_0(sK3,k2_tarski(sK2,sK4))),
% 1.69/0.60    inference(superposition,[],[f50,f124])).
% 1.69/0.60  fof(f124,plain,(
% 1.69/0.60    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 1.69/0.60    inference(superposition,[],[f94,f55])).
% 1.69/0.60  fof(f55,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.69/0.60    inference(cnf_transformation,[],[f15])).
% 1.69/0.60  fof(f15,axiom,(
% 1.69/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.69/0.60  fof(f94,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) )),
% 1.69/0.60    inference(superposition,[],[f55,f54])).
% 1.69/0.60  fof(f54,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.69/0.60    inference(cnf_transformation,[],[f11])).
% 1.69/0.60  fof(f11,axiom,(
% 1.69/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.69/0.60  fof(f50,plain,(
% 1.69/0.60    sK3 != k2_xboole_0(k2_tarski(sK2,sK4),sK3)),
% 1.69/0.60    inference(cnf_transformation,[],[f28])).
% 1.69/0.60  fof(f28,plain,(
% 1.69/0.60    sK3 != k2_xboole_0(k2_tarski(sK2,sK4),sK3) & r2_hidden(sK4,sK3) & r2_hidden(sK2,sK3)),
% 1.69/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f27])).
% 1.69/0.60  fof(f27,plain,(
% 1.69/0.60    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (sK3 != k2_xboole_0(k2_tarski(sK2,sK4),sK3) & r2_hidden(sK4,sK3) & r2_hidden(sK2,sK3))),
% 1.69/0.60    introduced(choice_axiom,[])).
% 1.69/0.60  fof(f20,plain,(
% 1.69/0.60    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 1.69/0.60    inference(flattening,[],[f19])).
% 1.69/0.60  fof(f19,plain,(
% 1.69/0.60    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 1.69/0.60    inference(ennf_transformation,[],[f18])).
% 1.69/0.60  fof(f18,negated_conjecture,(
% 1.69/0.60    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 1.69/0.60    inference(negated_conjecture,[],[f17])).
% 1.69/0.60  fof(f17,conjecture,(
% 1.69/0.60    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 1.69/0.60  fof(f487,plain,(
% 1.69/0.60    sK3 = k2_xboole_0(sK3,k2_tarski(sK2,sK4))),
% 1.69/0.60    inference(forward_demodulation,[],[f485,f52])).
% 1.69/0.60  fof(f52,plain,(
% 1.69/0.60    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.69/0.60    inference(cnf_transformation,[],[f7])).
% 1.69/0.60  fof(f7,axiom,(
% 1.69/0.60    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.69/0.60  fof(f485,plain,(
% 1.69/0.60    k2_xboole_0(sK3,k2_tarski(sK2,sK4)) = k2_xboole_0(sK3,k1_xboole_0)),
% 1.69/0.60    inference(superposition,[],[f58,f449])).
% 1.69/0.60  fof(f449,plain,(
% 1.69/0.60    k1_xboole_0 = k4_xboole_0(k2_tarski(sK2,sK4),sK3)),
% 1.69/0.60    inference(backward_demodulation,[],[f283,f447])).
% 1.69/0.60  fof(f447,plain,(
% 1.69/0.60    ( ! [X4] : (k1_xboole_0 = k5_xboole_0(X4,X4)) )),
% 1.69/0.60    inference(backward_demodulation,[],[f138,f446])).
% 1.69/0.60  fof(f446,plain,(
% 1.69/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.69/0.60    inference(duplicate_literal_removal,[],[f435])).
% 1.69/0.60  fof(f435,plain,(
% 1.69/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0) | k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.69/0.60    inference(resolution,[],[f349,f348])).
% 1.69/0.60  fof(f348,plain,(
% 1.69/0.60    ( ! [X8,X9] : (~r2_hidden(sK5(k4_xboole_0(X8,X9),k1_xboole_0),X9) | k1_xboole_0 = k4_xboole_0(X8,X9)) )),
% 1.69/0.60    inference(resolution,[],[f333,f208])).
% 1.69/0.60  fof(f208,plain,(
% 1.69/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | ~r2_hidden(X0,X2)) )),
% 1.69/0.60    inference(resolution,[],[f67,f88])).
% 1.69/0.60  fof(f88,plain,(
% 1.69/0.60    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 1.69/0.60    inference(equality_resolution,[],[f72])).
% 1.69/0.60  fof(f72,plain,(
% 1.69/0.60    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.69/0.60    inference(cnf_transformation,[],[f39])).
% 1.69/0.60  fof(f39,plain,(
% 1.69/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.69/0.60    inference(nnf_transformation,[],[f24])).
% 1.69/0.60  fof(f24,plain,(
% 1.69/0.60    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.69/0.60    inference(definition_folding,[],[f3,f23])).
% 1.69/0.60  fof(f23,plain,(
% 1.69/0.60    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.69/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.69/0.60  fof(f3,axiom,(
% 1.69/0.60    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.69/0.60  fof(f67,plain,(
% 1.69/0.60    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 1.69/0.60    inference(cnf_transformation,[],[f38])).
% 1.69/0.60  fof(f38,plain,(
% 1.69/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.69/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).
% 1.69/0.60  fof(f37,plain,(
% 1.69/0.60    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.69/0.60    introduced(choice_axiom,[])).
% 1.69/0.60  fof(f36,plain,(
% 1.69/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.69/0.60    inference(rectify,[],[f35])).
% 1.69/0.60  fof(f35,plain,(
% 1.69/0.60    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.69/0.60    inference(flattening,[],[f34])).
% 1.69/0.60  fof(f34,plain,(
% 1.69/0.60    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.69/0.60    inference(nnf_transformation,[],[f23])).
% 1.69/0.60  fof(f333,plain,(
% 1.69/0.60    ( ! [X17] : (r2_hidden(sK5(X17,k1_xboole_0),X17) | k1_xboole_0 = X17) )),
% 1.69/0.60    inference(resolution,[],[f60,f212])).
% 1.69/0.60  fof(f212,plain,(
% 1.69/0.60    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.69/0.60    inference(condensation,[],[f209])).
% 1.69/0.60  fof(f209,plain,(
% 1.69/0.60    ( ! [X4,X3] : (~r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,X4)) )),
% 1.69/0.60    inference(resolution,[],[f67,f177])).
% 1.69/0.60  fof(f177,plain,(
% 1.69/0.60    ( ! [X3] : (sP0(X3,k1_xboole_0,k1_xboole_0)) )),
% 1.69/0.60    inference(backward_demodulation,[],[f155,f175])).
% 1.69/0.60  fof(f175,plain,(
% 1.69/0.60    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6)) )),
% 1.69/0.60    inference(backward_demodulation,[],[f140,f174])).
% 1.69/0.60  fof(f174,plain,(
% 1.69/0.60    ( ! [X5] : (k5_xboole_0(X5,k1_xboole_0) = X5) )),
% 1.69/0.60    inference(backward_demodulation,[],[f139,f173])).
% 1.69/0.60  fof(f173,plain,(
% 1.69/0.60    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = X6) )),
% 1.69/0.60    inference(forward_demodulation,[],[f167,f126])).
% 1.69/0.60  fof(f126,plain,(
% 1.69/0.60    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.69/0.60    inference(superposition,[],[f124,f52])).
% 1.69/0.60  fof(f167,plain,(
% 1.69/0.60    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X6)) )),
% 1.69/0.60    inference(superposition,[],[f58,f126])).
% 1.69/0.60  fof(f139,plain,(
% 1.69/0.60    ( ! [X5] : (k4_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X5,k1_xboole_0)) )),
% 1.69/0.60    inference(superposition,[],[f57,f98])).
% 1.69/0.60  fof(f98,plain,(
% 1.69/0.60    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 1.69/0.60    inference(superposition,[],[f96,f53])).
% 1.69/0.60  fof(f53,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.69/0.60    inference(cnf_transformation,[],[f1])).
% 1.69/0.60  fof(f1,axiom,(
% 1.69/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.69/0.60  fof(f96,plain,(
% 1.69/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.69/0.60    inference(resolution,[],[f59,f51])).
% 1.69/0.60  fof(f51,plain,(
% 1.69/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.69/0.60    inference(cnf_transformation,[],[f9])).
% 1.69/0.60  fof(f9,axiom,(
% 1.69/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.69/0.60  fof(f59,plain,(
% 1.69/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.69/0.60    inference(cnf_transformation,[],[f21])).
% 1.69/0.60  fof(f21,plain,(
% 1.69/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.69/0.60    inference(ennf_transformation,[],[f8])).
% 1.69/0.60  fof(f8,axiom,(
% 1.69/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.69/0.60  fof(f57,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.69/0.60    inference(cnf_transformation,[],[f6])).
% 1.69/0.60  fof(f6,axiom,(
% 1.69/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.69/0.60  fof(f140,plain,(
% 1.69/0.60    ( ! [X6] : (k4_xboole_0(k1_xboole_0,X6) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.69/0.60    inference(superposition,[],[f57,f96])).
% 1.69/0.60  fof(f155,plain,(
% 1.69/0.60    ( ! [X2,X3] : (sP0(X3,k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) )),
% 1.69/0.60    inference(superposition,[],[f145,f141])).
% 1.69/0.60  fof(f141,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,X1)) )),
% 1.69/0.60    inference(superposition,[],[f140,f140])).
% 1.69/0.60  fof(f145,plain,(
% 1.69/0.60    ( ! [X0] : (sP0(X0,k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 1.69/0.60    inference(forward_demodulation,[],[f143,f138])).
% 1.69/0.60  fof(f143,plain,(
% 1.69/0.60    ( ! [X0] : (sP0(X0,k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 1.69/0.60    inference(superposition,[],[f88,f140])).
% 1.69/0.60  fof(f60,plain,(
% 1.69/0.60    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0) | X0 = X1) )),
% 1.69/0.60    inference(cnf_transformation,[],[f31])).
% 1.69/0.60  fof(f31,plain,(
% 1.69/0.60    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(sK5(X0,X1),X0)) & (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0))))),
% 1.69/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).
% 1.69/0.60  fof(f30,plain,(
% 1.69/0.60    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(sK5(X0,X1),X0)) & (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0))))),
% 1.69/0.60    introduced(choice_axiom,[])).
% 1.69/0.60  fof(f29,plain,(
% 1.69/0.60    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.69/0.60    inference(nnf_transformation,[],[f22])).
% 1.69/0.60  fof(f22,plain,(
% 1.69/0.60    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.69/0.60    inference(ennf_transformation,[],[f4])).
% 1.69/0.60  fof(f4,axiom,(
% 1.69/0.60    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.69/0.60  fof(f349,plain,(
% 1.69/0.60    ( ! [X10,X11] : (r2_hidden(sK5(k4_xboole_0(X10,X11),k1_xboole_0),X10) | k1_xboole_0 = k4_xboole_0(X10,X11)) )),
% 1.69/0.60    inference(resolution,[],[f333,f203])).
% 1.69/0.60  fof(f203,plain,(
% 1.69/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | r2_hidden(X0,X1)) )),
% 1.69/0.60    inference(resolution,[],[f66,f88])).
% 1.69/0.60  fof(f66,plain,(
% 1.69/0.60    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X1)) )),
% 1.69/0.60    inference(cnf_transformation,[],[f38])).
% 1.69/0.60  fof(f138,plain,(
% 1.69/0.60    ( ! [X4] : (k4_xboole_0(X4,X4) = k5_xboole_0(X4,X4)) )),
% 1.69/0.60    inference(superposition,[],[f57,f97])).
% 1.69/0.60  fof(f97,plain,(
% 1.69/0.60    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 1.69/0.60    inference(resolution,[],[f59,f86])).
% 1.69/0.60  fof(f86,plain,(
% 1.69/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.69/0.60    inference(equality_resolution,[],[f63])).
% 1.69/0.60  fof(f63,plain,(
% 1.69/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.69/0.60    inference(cnf_transformation,[],[f33])).
% 1.69/0.60  fof(f33,plain,(
% 1.69/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.69/0.60    inference(flattening,[],[f32])).
% 1.69/0.60  fof(f32,plain,(
% 1.69/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.69/0.60    inference(nnf_transformation,[],[f5])).
% 1.69/0.60  fof(f5,axiom,(
% 1.69/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.69/0.60  fof(f283,plain,(
% 1.69/0.60    k4_xboole_0(k2_tarski(sK2,sK4),sK3) = k5_xboole_0(k2_tarski(sK2,sK4),k2_tarski(sK2,sK4))),
% 1.69/0.60    inference(superposition,[],[f57,f254])).
% 1.69/0.60  fof(f254,plain,(
% 1.69/0.60    k2_tarski(sK2,sK4) = k3_xboole_0(k2_tarski(sK2,sK4),sK3)),
% 1.69/0.60    inference(resolution,[],[f246,f59])).
% 1.69/0.60  fof(f246,plain,(
% 1.69/0.60    r1_tarski(k2_tarski(sK2,sK4),sK3)),
% 1.69/0.60    inference(resolution,[],[f241,f49])).
% 1.69/0.60  fof(f49,plain,(
% 1.69/0.60    r2_hidden(sK4,sK3)),
% 1.69/0.60    inference(cnf_transformation,[],[f28])).
% 1.69/0.60  fof(f241,plain,(
% 1.69/0.60    ( ! [X0] : (~r2_hidden(X0,sK3) | r1_tarski(k2_tarski(sK2,X0),sK3)) )),
% 1.69/0.60    inference(resolution,[],[f84,f48])).
% 1.69/0.60  fof(f48,plain,(
% 1.69/0.60    r2_hidden(sK2,sK3)),
% 1.69/0.60    inference(cnf_transformation,[],[f28])).
% 1.69/0.60  fof(f84,plain,(
% 1.69/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.69/0.60    inference(cnf_transformation,[],[f47])).
% 1.69/0.60  fof(f47,plain,(
% 1.69/0.60    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.69/0.60    inference(flattening,[],[f46])).
% 1.69/0.60  fof(f46,plain,(
% 1.69/0.60    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.69/0.60    inference(nnf_transformation,[],[f16])).
% 1.69/0.60  fof(f16,axiom,(
% 1.69/0.60    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.69/0.60  fof(f58,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.69/0.60    inference(cnf_transformation,[],[f10])).
% 1.69/0.60  fof(f10,axiom,(
% 1.69/0.60    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.69/0.60  % SZS output end Proof for theBenchmark
% 1.69/0.60  % (20092)------------------------------
% 1.69/0.60  % (20092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.60  % (20092)Termination reason: Refutation
% 1.69/0.60  
% 1.69/0.60  % (20092)Memory used [KB]: 6524
% 1.69/0.60  % (20092)Time elapsed: 0.187 s
% 1.69/0.60  % (20092)------------------------------
% 1.69/0.60  % (20092)------------------------------
% 1.69/0.60  % (20080)Success in time 0.239 s
%------------------------------------------------------------------------------
