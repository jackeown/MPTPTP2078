%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:17 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 141 expanded)
%              Number of leaves         :   22 (  41 expanded)
%              Depth                    :   19
%              Number of atoms          :  245 ( 451 expanded)
%              Number of equality atoms :  144 ( 265 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1118,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1117,f45])).

fof(f45,plain,(
    sK1 != sK4 ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK1 != sK4
    & sK1 != sK3
    & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f23,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK1 != sK4
      & sK1 != sK3
      & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f1117,plain,(
    sK1 = sK4 ),
    inference(subsumption_resolution,[],[f1112,f44])).

fof(f44,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f32])).

fof(f1112,plain,
    ( sK1 = sK3
    | sK1 = sK4 ),
    inference(resolution,[],[f1100,f267])).

fof(f267,plain,(
    r2_hidden(sK1,k2_tarski(sK3,sK4)) ),
    inference(superposition,[],[f108,f265])).

fof(f265,plain,(
    k2_tarski(sK3,sK4) = k1_enumset1(sK3,sK4,sK1) ),
    inference(forward_demodulation,[],[f264,f47])).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f264,plain,(
    k5_xboole_0(k2_tarski(sK3,sK4),k1_xboole_0) = k1_enumset1(sK3,sK4,sK1) ),
    inference(forward_demodulation,[],[f262,f249])).

fof(f249,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f247,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f247,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(superposition,[],[f63,f53])).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f262,plain,(
    k5_xboole_0(k2_tarski(sK3,sK4),k1_xboole_0) = k2_xboole_0(k2_tarski(sK3,sK4),k1_tarski(sK1)) ),
    inference(superposition,[],[f54,f258])).

fof(f258,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k2_tarski(sK3,sK4)) ),
    inference(forward_demodulation,[],[f250,f148])).

fof(f148,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f127,f147])).

fof(f147,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f141,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f82,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f82,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(resolution,[],[f58,f46])).

fof(f46,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f141,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f56,f132])).

fof(f132,plain,(
    ! [X5] : k4_xboole_0(X5,k1_xboole_0) = X5 ),
    inference(forward_demodulation,[],[f130,f47])).

fof(f130,plain,(
    ! [X5] : k4_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X5,k1_xboole_0) ),
    inference(superposition,[],[f55,f83])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f127,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f55,f50])).

fof(f50,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f250,plain,(
    k4_xboole_0(k1_tarski(sK1),k2_tarski(sK3,sK4)) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) ),
    inference(superposition,[],[f55,f246])).

fof(f246,plain,(
    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k2_tarski(sK3,sK4)) ),
    inference(resolution,[],[f213,f51])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f213,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_tarski(sK1,sK2))
      | k3_xboole_0(X0,k2_tarski(sK3,sK4)) = X0 ) ),
    inference(resolution,[],[f205,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f205,plain,(
    ! [X1] :
      ( r1_tarski(X1,k2_tarski(sK3,sK4))
      | ~ r1_tarski(X1,k2_tarski(sK1,sK2)) ) ),
    inference(superposition,[],[f102,f100])).

fof(f100,plain,(
    k2_tarski(sK1,sK2) = k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(resolution,[],[f59,f43])).

fof(f43,plain,(
    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f32])).

fof(f102,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,k3_xboole_0(X3,X2))
      | r1_tarski(X4,X2) ) ),
    inference(superposition,[],[f61,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f108,plain,(
    ! [X6,X8,X7] : r2_hidden(X6,k1_enumset1(X7,X8,X6)) ),
    inference(resolution,[],[f77,f74])).

fof(f74,plain,(
    ! [X2,X5,X3,X1] :
      ( ~ sP0(X5,X1,X2,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK7(X0,X1,X2,X3) != X0
              & sK7(X0,X1,X2,X3) != X1
              & sK7(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
          & ( sK7(X0,X1,X2,X3) = X0
            | sK7(X0,X1,X2,X3) = X1
            | sK7(X0,X1,X2,X3) = X2
            | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).

fof(f40,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK7(X0,X1,X2,X3) != X0
            & sK7(X0,X1,X2,X3) != X1
            & sK7(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
        & ( sK7(X0,X1,X2,X3) = X0
          | sK7(X0,X1,X2,X3) = X1
          | sK7(X0,X1,X2,X3) = X2
          | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f77,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f30])).

% (10221)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f28,f29])).

fof(f28,plain,(
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

fof(f1100,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X5,k2_tarski(X4,X6))
      | X4 = X5
      | X5 = X6 ) ),
    inference(duplicate_literal_removal,[],[f1094])).

fof(f1094,plain,(
    ! [X6,X4,X5] :
      ( X4 = X5
      | X4 = X5
      | ~ r2_hidden(X5,k2_tarski(X4,X6))
      | X5 = X6 ) ),
    inference(resolution,[],[f64,f109])).

fof(f109,plain,(
    ! [X0,X1] : sP0(X1,X0,X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f77,f53])).

fof(f64,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | X1 = X5
      | X2 = X5
      | ~ r2_hidden(X5,X3)
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:25:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (10200)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (10216)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (10210)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (10193)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (10208)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (10210)Refutation not found, incomplete strategy% (10210)------------------------------
% 0.20/0.52  % (10210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10193)Refutation not found, incomplete strategy% (10193)------------------------------
% 0.20/0.52  % (10193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10193)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10193)Memory used [KB]: 1663
% 0.20/0.52  % (10193)Time elapsed: 0.110 s
% 0.20/0.52  % (10193)------------------------------
% 0.20/0.52  % (10193)------------------------------
% 0.20/0.52  % (10208)Refutation not found, incomplete strategy% (10208)------------------------------
% 0.20/0.52  % (10208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10210)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10210)Memory used [KB]: 10618
% 0.20/0.52  % (10210)Time elapsed: 0.121 s
% 0.20/0.52  % (10210)------------------------------
% 0.20/0.52  % (10210)------------------------------
% 0.20/0.53  % (10216)Refutation not found, incomplete strategy% (10216)------------------------------
% 0.20/0.53  % (10216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (10208)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (10208)Memory used [KB]: 6140
% 0.20/0.53  % (10208)Time elapsed: 0.113 s
% 0.20/0.53  % (10208)------------------------------
% 0.20/0.53  % (10208)------------------------------
% 0.20/0.53  % (10216)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (10216)Memory used [KB]: 1791
% 0.20/0.53  % (10216)Time elapsed: 0.115 s
% 0.20/0.53  % (10216)------------------------------
% 0.20/0.53  % (10216)------------------------------
% 0.20/0.53  % (10196)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (10197)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (10218)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (10195)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (10217)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (10195)Refutation not found, incomplete strategy% (10195)------------------------------
% 0.20/0.54  % (10195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (10195)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (10195)Memory used [KB]: 10746
% 0.20/0.54  % (10195)Time elapsed: 0.124 s
% 0.20/0.54  % (10195)------------------------------
% 0.20/0.54  % (10195)------------------------------
% 0.20/0.54  % (10209)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (10203)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (10206)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (10203)Refutation not found, incomplete strategy% (10203)------------------------------
% 0.20/0.55  % (10203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (10203)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (10203)Memory used [KB]: 10618
% 0.20/0.55  % (10203)Time elapsed: 0.139 s
% 0.20/0.55  % (10203)------------------------------
% 0.20/0.55  % (10203)------------------------------
% 0.20/0.55  % (10194)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.55  % (10198)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.55  % (10197)Refutation not found, incomplete strategy% (10197)------------------------------
% 0.20/0.55  % (10197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (10197)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (10197)Memory used [KB]: 6268
% 0.20/0.55  % (10197)Time elapsed: 0.141 s
% 0.20/0.55  % (10197)------------------------------
% 0.20/0.55  % (10197)------------------------------
% 0.20/0.56  % (10220)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.56  % (10212)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.56  % (10214)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.56  % (10202)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.56  % (10214)Refutation not found, incomplete strategy% (10214)------------------------------
% 0.20/0.56  % (10214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (10214)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (10214)Memory used [KB]: 1791
% 0.20/0.56  % (10214)Time elapsed: 0.141 s
% 0.20/0.56  % (10214)------------------------------
% 0.20/0.56  % (10214)------------------------------
% 0.20/0.56  % (10202)Refutation not found, incomplete strategy% (10202)------------------------------
% 0.20/0.56  % (10202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (10202)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (10202)Memory used [KB]: 10618
% 0.20/0.56  % (10202)Time elapsed: 0.146 s
% 0.20/0.56  % (10202)------------------------------
% 0.20/0.56  % (10202)------------------------------
% 0.20/0.56  % (10201)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.56  % (10201)Refutation not found, incomplete strategy% (10201)------------------------------
% 0.20/0.56  % (10201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (10201)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (10201)Memory used [KB]: 10746
% 0.20/0.56  % (10201)Time elapsed: 0.120 s
% 0.20/0.56  % (10201)------------------------------
% 0.20/0.56  % (10201)------------------------------
% 0.20/0.57  % (10222)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.57  % (10211)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.57  % (10204)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.57  % (10207)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.57  % (10213)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.57  % (10215)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.58  % (10219)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.71/0.58  % (10205)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.71/0.58  % (10199)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.71/0.58  % (10200)Refutation found. Thanks to Tanya!
% 1.71/0.58  % SZS status Theorem for theBenchmark
% 1.71/0.58  % SZS output start Proof for theBenchmark
% 1.71/0.58  fof(f1118,plain,(
% 1.71/0.58    $false),
% 1.71/0.58    inference(subsumption_resolution,[],[f1117,f45])).
% 1.71/0.58  fof(f45,plain,(
% 1.71/0.58    sK1 != sK4),
% 1.71/0.58    inference(cnf_transformation,[],[f32])).
% 1.71/0.58  fof(f32,plain,(
% 1.71/0.58    sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 1.71/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f23,f31])).
% 1.71/0.58  fof(f31,plain,(
% 1.71/0.58    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 1.71/0.58    introduced(choice_axiom,[])).
% 1.71/0.58  fof(f23,plain,(
% 1.71/0.58    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.71/0.58    inference(ennf_transformation,[],[f20])).
% 1.71/0.58  fof(f20,negated_conjecture,(
% 1.71/0.58    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.71/0.58    inference(negated_conjecture,[],[f19])).
% 1.71/0.58  fof(f19,conjecture,(
% 1.71/0.58    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 1.71/0.58  fof(f1117,plain,(
% 1.71/0.58    sK1 = sK4),
% 1.71/0.58    inference(subsumption_resolution,[],[f1112,f44])).
% 1.71/0.58  fof(f44,plain,(
% 1.71/0.58    sK1 != sK3),
% 1.71/0.58    inference(cnf_transformation,[],[f32])).
% 1.71/0.58  fof(f1112,plain,(
% 1.71/0.58    sK1 = sK3 | sK1 = sK4),
% 1.71/0.58    inference(resolution,[],[f1100,f267])).
% 1.71/0.58  fof(f267,plain,(
% 1.71/0.58    r2_hidden(sK1,k2_tarski(sK3,sK4))),
% 1.71/0.58    inference(superposition,[],[f108,f265])).
% 1.71/0.58  fof(f265,plain,(
% 1.71/0.58    k2_tarski(sK3,sK4) = k1_enumset1(sK3,sK4,sK1)),
% 1.71/0.58    inference(forward_demodulation,[],[f264,f47])).
% 1.71/0.58  fof(f47,plain,(
% 1.71/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.71/0.58    inference(cnf_transformation,[],[f9])).
% 1.71/0.58  fof(f9,axiom,(
% 1.71/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.71/0.58  fof(f264,plain,(
% 1.71/0.58    k5_xboole_0(k2_tarski(sK3,sK4),k1_xboole_0) = k1_enumset1(sK3,sK4,sK1)),
% 1.71/0.58    inference(forward_demodulation,[],[f262,f249])).
% 1.71/0.58  fof(f249,plain,(
% 1.71/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.71/0.58    inference(forward_demodulation,[],[f247,f60])).
% 1.71/0.58  fof(f60,plain,(
% 1.71/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f16])).
% 1.71/0.58  fof(f16,axiom,(
% 1.71/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.71/0.58  fof(f247,plain,(
% 1.71/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.71/0.58    inference(superposition,[],[f63,f53])).
% 1.71/0.58  fof(f53,plain,(
% 1.71/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f15])).
% 1.71/0.58  fof(f15,axiom,(
% 1.71/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.71/0.58  fof(f63,plain,(
% 1.71/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.71/0.58    inference(cnf_transformation,[],[f13])).
% 1.71/0.58  fof(f13,axiom,(
% 1.71/0.58    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 1.71/0.58  fof(f262,plain,(
% 1.71/0.58    k5_xboole_0(k2_tarski(sK3,sK4),k1_xboole_0) = k2_xboole_0(k2_tarski(sK3,sK4),k1_tarski(sK1))),
% 1.71/0.58    inference(superposition,[],[f54,f258])).
% 1.71/0.58  fof(f258,plain,(
% 1.71/0.58    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k2_tarski(sK3,sK4))),
% 1.71/0.58    inference(forward_demodulation,[],[f250,f148])).
% 1.71/0.58  fof(f148,plain,(
% 1.71/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.71/0.58    inference(backward_demodulation,[],[f127,f147])).
% 1.71/0.58  fof(f147,plain,(
% 1.71/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.71/0.58    inference(forward_demodulation,[],[f141,f83])).
% 1.71/0.58  fof(f83,plain,(
% 1.71/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.71/0.58    inference(resolution,[],[f82,f49])).
% 1.71/0.58  fof(f49,plain,(
% 1.71/0.58    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 1.71/0.58    inference(cnf_transformation,[],[f34])).
% 1.71/0.58  fof(f34,plain,(
% 1.71/0.58    ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0)),
% 1.71/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f33])).
% 1.71/0.58  fof(f33,plain,(
% 1.71/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 1.71/0.58    introduced(choice_axiom,[])).
% 1.71/0.58  fof(f24,plain,(
% 1.71/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.71/0.58    inference(ennf_transformation,[],[f4])).
% 1.71/0.58  fof(f4,axiom,(
% 1.71/0.58    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.71/0.58  fof(f82,plain,(
% 1.71/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 1.71/0.58    inference(resolution,[],[f58,f46])).
% 1.71/0.58  fof(f46,plain,(
% 1.71/0.58    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f10])).
% 1.71/0.58  fof(f10,axiom,(
% 1.71/0.58    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.71/0.58  fof(f58,plain,(
% 1.71/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.71/0.58    inference(cnf_transformation,[],[f36])).
% 1.71/0.58  fof(f36,plain,(
% 1.71/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.71/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f35])).
% 1.71/0.58  fof(f35,plain,(
% 1.71/0.58    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)))),
% 1.71/0.58    introduced(choice_axiom,[])).
% 1.71/0.58  fof(f25,plain,(
% 1.71/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.71/0.58    inference(ennf_transformation,[],[f22])).
% 1.71/0.58  fof(f22,plain,(
% 1.71/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.71/0.58    inference(rectify,[],[f3])).
% 1.71/0.58  fof(f3,axiom,(
% 1.71/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.71/0.58  fof(f141,plain,(
% 1.71/0.58    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 1.71/0.58    inference(superposition,[],[f56,f132])).
% 1.71/0.58  fof(f132,plain,(
% 1.71/0.58    ( ! [X5] : (k4_xboole_0(X5,k1_xboole_0) = X5) )),
% 1.71/0.58    inference(forward_demodulation,[],[f130,f47])).
% 1.71/0.58  fof(f130,plain,(
% 1.71/0.58    ( ! [X5] : (k4_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X5,k1_xboole_0)) )),
% 1.71/0.58    inference(superposition,[],[f55,f83])).
% 1.71/0.58  fof(f55,plain,(
% 1.71/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.71/0.58    inference(cnf_transformation,[],[f5])).
% 1.71/0.58  fof(f5,axiom,(
% 1.71/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.71/0.58  fof(f56,plain,(
% 1.71/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.71/0.58    inference(cnf_transformation,[],[f8])).
% 1.71/0.58  fof(f8,axiom,(
% 1.71/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.71/0.58  fof(f127,plain,(
% 1.71/0.58    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.71/0.58    inference(superposition,[],[f55,f50])).
% 1.71/0.58  fof(f50,plain,(
% 1.71/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.71/0.58    inference(cnf_transformation,[],[f21])).
% 1.71/0.58  fof(f21,plain,(
% 1.71/0.58    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.71/0.58    inference(rectify,[],[f2])).
% 1.71/0.58  fof(f2,axiom,(
% 1.71/0.58    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.71/0.58  fof(f250,plain,(
% 1.71/0.58    k4_xboole_0(k1_tarski(sK1),k2_tarski(sK3,sK4)) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1))),
% 1.71/0.58    inference(superposition,[],[f55,f246])).
% 1.71/0.58  fof(f246,plain,(
% 1.71/0.58    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k2_tarski(sK3,sK4))),
% 1.71/0.58    inference(resolution,[],[f213,f51])).
% 1.71/0.58  fof(f51,plain,(
% 1.71/0.58    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.71/0.58    inference(cnf_transformation,[],[f18])).
% 1.71/0.58  fof(f18,axiom,(
% 1.71/0.58    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.71/0.58  fof(f213,plain,(
% 1.71/0.58    ( ! [X0] : (~r1_tarski(X0,k2_tarski(sK1,sK2)) | k3_xboole_0(X0,k2_tarski(sK3,sK4)) = X0) )),
% 1.71/0.58    inference(resolution,[],[f205,f59])).
% 1.71/0.58  fof(f59,plain,(
% 1.71/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.71/0.58    inference(cnf_transformation,[],[f26])).
% 1.71/0.58  fof(f26,plain,(
% 1.71/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.71/0.58    inference(ennf_transformation,[],[f7])).
% 1.71/0.58  fof(f7,axiom,(
% 1.71/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.71/0.58  fof(f205,plain,(
% 1.71/0.58    ( ! [X1] : (r1_tarski(X1,k2_tarski(sK3,sK4)) | ~r1_tarski(X1,k2_tarski(sK1,sK2))) )),
% 1.71/0.58    inference(superposition,[],[f102,f100])).
% 1.71/0.58  fof(f100,plain,(
% 1.71/0.58    k2_tarski(sK1,sK2) = k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 1.71/0.58    inference(resolution,[],[f59,f43])).
% 1.71/0.58  fof(f43,plain,(
% 1.71/0.58    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 1.71/0.58    inference(cnf_transformation,[],[f32])).
% 1.71/0.58  fof(f102,plain,(
% 1.71/0.58    ( ! [X4,X2,X3] : (~r1_tarski(X4,k3_xboole_0(X3,X2)) | r1_tarski(X4,X2)) )),
% 1.71/0.58    inference(superposition,[],[f61,f52])).
% 1.71/0.58  fof(f52,plain,(
% 1.71/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f1])).
% 1.71/0.58  fof(f1,axiom,(
% 1.71/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.71/0.58  fof(f61,plain,(
% 1.71/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f27])).
% 1.71/0.58  fof(f27,plain,(
% 1.71/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.71/0.58    inference(ennf_transformation,[],[f6])).
% 1.71/0.58  fof(f6,axiom,(
% 1.71/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 1.71/0.58  fof(f54,plain,(
% 1.71/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.71/0.58    inference(cnf_transformation,[],[f11])).
% 1.71/0.58  fof(f11,axiom,(
% 1.71/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.71/0.58  fof(f108,plain,(
% 1.71/0.58    ( ! [X6,X8,X7] : (r2_hidden(X6,k1_enumset1(X7,X8,X6))) )),
% 1.71/0.58    inference(resolution,[],[f77,f74])).
% 1.71/0.58  fof(f74,plain,(
% 1.71/0.58    ( ! [X2,X5,X3,X1] : (~sP0(X5,X1,X2,X3) | r2_hidden(X5,X3)) )),
% 1.71/0.58    inference(equality_resolution,[],[f67])).
% 1.71/0.58  fof(f67,plain,(
% 1.71/0.58    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f41])).
% 1.71/0.58  fof(f41,plain,(
% 1.71/0.58    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK7(X0,X1,X2,X3) != X0 & sK7(X0,X1,X2,X3) != X1 & sK7(X0,X1,X2,X3) != X2) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sK7(X0,X1,X2,X3) = X0 | sK7(X0,X1,X2,X3) = X1 | sK7(X0,X1,X2,X3) = X2 | r2_hidden(sK7(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.71/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).
% 1.71/0.58  fof(f40,plain,(
% 1.71/0.58    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK7(X0,X1,X2,X3) != X0 & sK7(X0,X1,X2,X3) != X1 & sK7(X0,X1,X2,X3) != X2) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sK7(X0,X1,X2,X3) = X0 | sK7(X0,X1,X2,X3) = X1 | sK7(X0,X1,X2,X3) = X2 | r2_hidden(sK7(X0,X1,X2,X3),X3))))),
% 1.71/0.58    introduced(choice_axiom,[])).
% 1.71/0.58  fof(f39,plain,(
% 1.71/0.58    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.71/0.58    inference(rectify,[],[f38])).
% 1.71/0.58  fof(f38,plain,(
% 1.71/0.58    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.71/0.58    inference(flattening,[],[f37])).
% 1.71/0.58  fof(f37,plain,(
% 1.71/0.58    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.71/0.58    inference(nnf_transformation,[],[f29])).
% 1.71/0.58  fof(f29,plain,(
% 1.71/0.58    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.71/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.71/0.58  fof(f77,plain,(
% 1.71/0.58    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 1.71/0.58    inference(equality_resolution,[],[f72])).
% 1.71/0.58  fof(f72,plain,(
% 1.71/0.58    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.71/0.58    inference(cnf_transformation,[],[f42])).
% 1.71/0.58  fof(f42,plain,(
% 1.71/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.71/0.58    inference(nnf_transformation,[],[f30])).
% 1.71/0.58  % (10221)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.71/0.58  fof(f30,plain,(
% 1.71/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 1.71/0.58    inference(definition_folding,[],[f28,f29])).
% 1.71/0.58  fof(f28,plain,(
% 1.71/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.71/0.58    inference(ennf_transformation,[],[f12])).
% 1.71/0.58  fof(f12,axiom,(
% 1.71/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.71/0.58  fof(f1100,plain,(
% 1.71/0.58    ( ! [X6,X4,X5] : (~r2_hidden(X5,k2_tarski(X4,X6)) | X4 = X5 | X5 = X6) )),
% 1.71/0.58    inference(duplicate_literal_removal,[],[f1094])).
% 1.71/0.58  fof(f1094,plain,(
% 1.71/0.58    ( ! [X6,X4,X5] : (X4 = X5 | X4 = X5 | ~r2_hidden(X5,k2_tarski(X4,X6)) | X5 = X6) )),
% 1.71/0.58    inference(resolution,[],[f64,f109])).
% 1.71/0.58  fof(f109,plain,(
% 1.71/0.58    ( ! [X0,X1] : (sP0(X1,X0,X0,k2_tarski(X0,X1))) )),
% 1.71/0.58    inference(superposition,[],[f77,f53])).
% 1.71/0.58  fof(f64,plain,(
% 1.71/0.58    ( ! [X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3) | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3) | X0 = X5) )),
% 1.71/0.58    inference(cnf_transformation,[],[f41])).
% 1.71/0.58  % SZS output end Proof for theBenchmark
% 1.71/0.58  % (10200)------------------------------
% 1.71/0.58  % (10200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.58  % (10200)Termination reason: Refutation
% 1.71/0.58  
% 1.71/0.58  % (10200)Memory used [KB]: 7164
% 1.71/0.58  % (10200)Time elapsed: 0.153 s
% 1.71/0.58  % (10200)------------------------------
% 1.71/0.58  % (10200)------------------------------
% 1.71/0.59  % (10192)Success in time 0.223 s
%------------------------------------------------------------------------------
