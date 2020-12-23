%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  150 (1158 expanded)
%              Number of leaves         :   18 ( 354 expanded)
%              Depth                    :   27
%              Number of atoms          :  225 (2352 expanded)
%              Number of equality atoms :  127 (1181 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1192,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1190])).

fof(f1190,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f36,f1105])).

fof(f1105,plain,(
    sK1 = sK2 ),
    inference(backward_demodulation,[],[f1010,f1044])).

fof(f1044,plain,(
    sK1 = k4_xboole_0(sK1,sK0) ),
    inference(backward_demodulation,[],[f313,f1030])).

fof(f1030,plain,(
    sK0 = sK3 ),
    inference(forward_demodulation,[],[f1029,f309])).

fof(f309,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f290,f38])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f290,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f55,f183])).

fof(f183,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f181,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f181,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f180,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f48,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f180,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,
    ( r1_xboole_0(sK0,sK2)
    | r1_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f96,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
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
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f96,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK6(X1,sK2),sK0)
      | r1_xboole_0(X1,sK2) ) ),
    inference(resolution,[],[f92,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f51,f34])).

fof(f34,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f42])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f1029,plain,(
    sK3 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f1024,f760])).

fof(f760,plain,(
    sK3 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f604,f759])).

fof(f759,plain,(
    sK3 = k4_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f754,f38])).

fof(f754,plain,(
    k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,sK2) ),
    inference(superposition,[],[f454,f740])).

fof(f740,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f737,f340])).

fof(f340,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[],[f52,f317])).

fof(f317,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f292,f38])).

fof(f292,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f55,f123])).

fof(f123,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f121,f39])).

fof(f121,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))) ),
    inference(resolution,[],[f57,f34])).

fof(f52,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f737,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f734,f175])).

fof(f175,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f162,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f162,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f52,f59])).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f54,f38])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f37,f42])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f734,plain,(
    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f340,f482])).

fof(f482,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f373,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f373,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(superposition,[],[f324,f33])).

fof(f33,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f324,plain,(
    ! [X2] : k2_xboole_0(sK2,X2) = k2_xboole_0(k2_xboole_0(sK2,X2),sK2) ),
    inference(backward_demodulation,[],[f263,f317])).

fof(f263,plain,(
    ! [X2] : k2_xboole_0(k4_xboole_0(sK2,sK0),X2) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK0),X2),sK2) ),
    inference(forward_demodulation,[],[f262,f62])).

fof(f62,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f61,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f61,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f60,f40])).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f60,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f44,f59])).

fof(f262,plain,(
    ! [X2] : k2_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK0),X2),sK2) = k2_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK2,sK0),X2)) ),
    inference(forward_demodulation,[],[f259,f41])).

fof(f259,plain,(
    ! [X2] : k2_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK0),X2),sK2) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK0),X2),k1_xboole_0) ),
    inference(superposition,[],[f44,f171])).

fof(f171,plain,(
    ! [X12] : k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X12)) ),
    inference(forward_demodulation,[],[f158,f82])).

fof(f82,plain,(
    ! [X8] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X8) ),
    inference(forward_demodulation,[],[f78,f59])).

fof(f78,plain,(
    ! [X8] : k4_xboole_0(k1_xboole_0,X8) = k4_xboole_0(X8,X8) ),
    inference(superposition,[],[f45,f62])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f158,plain,(
    ! [X12] : k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X12)) = k4_xboole_0(k1_xboole_0,X12) ),
    inference(superposition,[],[f52,f123])).

fof(f454,plain,(
    ! [X2] : k4_xboole_0(sK3,k4_xboole_0(X2,sK1)) = k4_xboole_0(sK3,X2) ),
    inference(forward_demodulation,[],[f448,f343])).

fof(f343,plain,(
    ! [X0] : k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[],[f52,f325])).

fof(f325,plain,(
    sK3 = k4_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f293,f38])).

fof(f293,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f55,f141])).

fof(f141,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f122,f39])).

fof(f122,plain,(
    ! [X1] : ~ r2_hidden(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) ),
    inference(resolution,[],[f57,f35])).

fof(f35,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f448,plain,(
    ! [X2] : k4_xboole_0(sK3,k4_xboole_0(X2,sK1)) = k4_xboole_0(sK3,k2_xboole_0(sK1,X2)) ),
    inference(superposition,[],[f343,f44])).

fof(f604,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k4_xboole_0(sK3,sK2) ),
    inference(superposition,[],[f45,f598])).

fof(f598,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f597,f89])).

fof(f89,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f88,f33])).

fof(f88,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f87,f41])).

fof(f87,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f86,f44])).

fof(f86,plain,(
    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f44,f74])).

fof(f74,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(superposition,[],[f45,f33])).

fof(f597,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f44,f578])).

fof(f578,plain,(
    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(backward_demodulation,[],[f74,f575])).

fof(f575,plain,(
    sK2 = k4_xboole_0(sK2,sK3) ),
    inference(forward_demodulation,[],[f570,f38])).

fof(f570,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f440,f559])).

fof(f559,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK0) ),
    inference(superposition,[],[f445,f91])).

fof(f91,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f90,f59])).

fof(f90,plain,(
    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f45,f89])).

fof(f445,plain,(
    ! [X0] : k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f343,f41])).

fof(f440,plain,(
    ! [X2] : k4_xboole_0(sK2,k4_xboole_0(X2,sK0)) = k4_xboole_0(sK2,X2) ),
    inference(forward_demodulation,[],[f434,f340])).

fof(f434,plain,(
    ! [X2] : k4_xboole_0(sK2,k4_xboole_0(X2,sK0)) = k4_xboole_0(sK2,k2_xboole_0(sK0,X2)) ),
    inference(superposition,[],[f340,f44])).

fof(f1024,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(superposition,[],[f45,f995])).

fof(f995,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f992,f41])).

fof(f992,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f982,f85])).

fof(f85,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X2,k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f81,f44])).

fof(f81,plain,(
    ! [X2,X1] : k2_xboole_0(X2,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f44,f45])).

fof(f982,plain,(
    k2_xboole_0(sK2,sK0) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f221,f969])).

fof(f969,plain,(
    sK0 = k2_xboole_0(sK3,sK0) ),
    inference(superposition,[],[f518,f583])).

fof(f583,plain,(
    sK0 = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f582,f62])).

fof(f582,plain,(
    k2_xboole_0(sK0,sK3) = k2_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f574,f41])).

fof(f574,plain,(
    k2_xboole_0(sK0,sK3) = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f44,f559])).

fof(f518,plain,(
    ! [X2] : k2_xboole_0(X2,sK3) = k2_xboole_0(sK3,k2_xboole_0(X2,sK3)) ),
    inference(superposition,[],[f419,f41])).

fof(f419,plain,(
    ! [X0] : k2_xboole_0(X0,sK3) = k2_xboole_0(k2_xboole_0(X0,sK3),sK3) ),
    inference(superposition,[],[f332,f41])).

fof(f332,plain,(
    ! [X2] : k2_xboole_0(sK3,X2) = k2_xboole_0(k2_xboole_0(sK3,X2),sK3) ),
    inference(backward_demodulation,[],[f275,f325])).

fof(f275,plain,(
    ! [X2] : k2_xboole_0(k4_xboole_0(sK3,sK1),X2) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK3,sK1),X2),sK3) ),
    inference(forward_demodulation,[],[f274,f62])).

fof(f274,plain,(
    ! [X2] : k2_xboole_0(k2_xboole_0(k4_xboole_0(sK3,sK1),X2),sK3) = k2_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK3,sK1),X2)) ),
    inference(forward_demodulation,[],[f271,f41])).

fof(f271,plain,(
    ! [X2] : k2_xboole_0(k2_xboole_0(k4_xboole_0(sK3,sK1),X2),sK3) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK3,sK1),X2),k1_xboole_0) ),
    inference(superposition,[],[f44,f174])).

fof(f174,plain,(
    ! [X14] : k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X14)) ),
    inference(forward_demodulation,[],[f160,f82])).

fof(f160,plain,(
    ! [X14] : k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X14)) = k4_xboole_0(k1_xboole_0,X14) ),
    inference(superposition,[],[f52,f141])).

fof(f221,plain,(
    ! [X19] : k2_xboole_0(sK2,k2_xboole_0(sK3,X19)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X19)) ),
    inference(forward_demodulation,[],[f205,f53])).

fof(f205,plain,(
    ! [X19] : k2_xboole_0(sK2,k2_xboole_0(sK3,X19)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X19) ),
    inference(superposition,[],[f53,f33])).

fof(f313,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f291,f38])).

fof(f291,plain,(
    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f55,f231])).

fof(f231,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f229,f39])).

fof(f229,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) ),
    inference(resolution,[],[f197,f57])).

fof(f197,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,
    ( r1_xboole_0(sK1,sK3)
    | r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f108,f49])).

fof(f108,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK6(X1,sK3),sK1)
      | r1_xboole_0(X1,sK3) ) ),
    inference(resolution,[],[f93,f50])).

fof(f93,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f51,f35])).

fof(f1010,plain,(
    sK2 = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f1009,f317])).

fof(f1009,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f1003,f75])).

fof(f75,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f45,f41])).

fof(f1003,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f45,f992])).

fof(f36,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (22564)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (22575)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.50  % (22584)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (22588)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.51  % (22562)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (22583)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (22567)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (22569)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (22576)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (22566)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (22580)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (22570)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (22563)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (22587)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.52  % (22568)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (22577)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (22579)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (22573)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (22574)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (22586)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (22579)Refutation not found, incomplete strategy% (22579)------------------------------
% 0.20/0.52  % (22579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (22579)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (22579)Memory used [KB]: 10618
% 0.20/0.52  % (22579)Time elapsed: 0.113 s
% 0.20/0.52  % (22579)------------------------------
% 0.20/0.52  % (22579)------------------------------
% 0.20/0.52  % (22565)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (22571)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (22572)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (22578)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (22591)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (22589)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (22582)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (22581)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (22585)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (22590)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.58  % (22574)Refutation found. Thanks to Tanya!
% 0.20/0.58  % SZS status Theorem for theBenchmark
% 0.20/0.58  % SZS output start Proof for theBenchmark
% 0.20/0.58  fof(f1192,plain,(
% 0.20/0.58    $false),
% 0.20/0.58    inference(trivial_inequality_removal,[],[f1190])).
% 0.20/0.58  fof(f1190,plain,(
% 0.20/0.58    sK1 != sK1),
% 0.20/0.58    inference(superposition,[],[f36,f1105])).
% 0.20/0.58  fof(f1105,plain,(
% 0.20/0.58    sK1 = sK2),
% 0.20/0.58    inference(backward_demodulation,[],[f1010,f1044])).
% 0.20/0.58  fof(f1044,plain,(
% 0.20/0.58    sK1 = k4_xboole_0(sK1,sK0)),
% 0.20/0.58    inference(backward_demodulation,[],[f313,f1030])).
% 0.20/0.58  fof(f1030,plain,(
% 0.20/0.58    sK0 = sK3),
% 0.20/0.58    inference(forward_demodulation,[],[f1029,f309])).
% 0.20/0.58  fof(f309,plain,(
% 0.20/0.58    sK0 = k4_xboole_0(sK0,sK2)),
% 0.20/0.58    inference(forward_demodulation,[],[f290,f38])).
% 0.20/0.58  fof(f38,plain,(
% 0.20/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f8])).
% 0.20/0.58  fof(f8,axiom,(
% 0.20/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.58  fof(f290,plain,(
% 0.20/0.58    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)),
% 0.20/0.58    inference(superposition,[],[f55,f183])).
% 0.20/0.58  fof(f183,plain,(
% 0.20/0.58    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.20/0.58    inference(resolution,[],[f181,f39])).
% 0.20/0.58  fof(f39,plain,(
% 0.20/0.58    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f28])).
% 0.20/0.58  fof(f28,plain,(
% 0.20/0.58    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f27])).
% 1.80/0.60  fof(f27,plain,(
% 1.80/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.80/0.60    introduced(choice_axiom,[])).
% 1.80/0.60  fof(f22,plain,(
% 1.80/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.80/0.60    inference(ennf_transformation,[],[f5])).
% 1.80/0.60  fof(f5,axiom,(
% 1.80/0.60    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.80/0.60  fof(f181,plain,(
% 1.80/0.60    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) )),
% 1.80/0.60    inference(resolution,[],[f180,f57])).
% 1.80/0.60  fof(f57,plain,(
% 1.80/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.80/0.60    inference(definition_unfolding,[],[f48,f42])).
% 1.80/0.60  fof(f42,plain,(
% 1.80/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.80/0.60    inference(cnf_transformation,[],[f12])).
% 1.80/0.60  fof(f12,axiom,(
% 1.80/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.80/0.60  fof(f48,plain,(
% 1.80/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.80/0.60    inference(cnf_transformation,[],[f30])).
% 1.80/0.60  fof(f30,plain,(
% 1.80/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.80/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f29])).
% 1.80/0.60  fof(f29,plain,(
% 1.80/0.60    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 1.80/0.60    introduced(choice_axiom,[])).
% 1.80/0.60  fof(f23,plain,(
% 1.80/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.80/0.60    inference(ennf_transformation,[],[f18])).
% 1.80/0.60  fof(f18,plain,(
% 1.80/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.80/0.60    inference(rectify,[],[f4])).
% 1.80/0.60  fof(f4,axiom,(
% 1.80/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.80/0.60  fof(f180,plain,(
% 1.80/0.60    r1_xboole_0(sK0,sK2)),
% 1.80/0.60    inference(duplicate_literal_removal,[],[f179])).
% 1.80/0.60  fof(f179,plain,(
% 1.80/0.60    r1_xboole_0(sK0,sK2) | r1_xboole_0(sK0,sK2)),
% 1.80/0.60    inference(resolution,[],[f96,f49])).
% 1.80/0.60  fof(f49,plain,(
% 1.80/0.60    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f32])).
% 1.80/0.60  fof(f32,plain,(
% 1.80/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.80/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f31])).
% 1.80/0.60  fof(f31,plain,(
% 1.80/0.60    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.80/0.60    introduced(choice_axiom,[])).
% 1.80/0.60  fof(f24,plain,(
% 1.80/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.80/0.60    inference(ennf_transformation,[],[f19])).
% 1.80/0.60  fof(f19,plain,(
% 1.80/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.80/0.60    inference(rectify,[],[f3])).
% 1.80/0.60  fof(f3,axiom,(
% 1.80/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.80/0.60  fof(f96,plain,(
% 1.80/0.60    ( ! [X1] : (~r2_hidden(sK6(X1,sK2),sK0) | r1_xboole_0(X1,sK2)) )),
% 1.80/0.60    inference(resolution,[],[f92,f50])).
% 1.80/0.60  fof(f50,plain,(
% 1.80/0.60    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f32])).
% 1.80/0.60  fof(f92,plain,(
% 1.80/0.60    ( ! [X0] : (~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) )),
% 1.80/0.60    inference(resolution,[],[f51,f34])).
% 1.80/0.60  fof(f34,plain,(
% 1.80/0.60    r1_xboole_0(sK2,sK0)),
% 1.80/0.60    inference(cnf_transformation,[],[f26])).
% 1.80/0.60  fof(f26,plain,(
% 1.80/0.60    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.80/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f25])).
% 1.80/0.60  fof(f25,plain,(
% 1.80/0.60    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 1.80/0.60    introduced(choice_axiom,[])).
% 1.80/0.60  fof(f21,plain,(
% 1.80/0.60    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 1.80/0.60    inference(flattening,[],[f20])).
% 1.80/0.60  fof(f20,plain,(
% 1.80/0.60    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 1.80/0.60    inference(ennf_transformation,[],[f16])).
% 1.80/0.60  fof(f16,negated_conjecture,(
% 1.80/0.60    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.80/0.60    inference(negated_conjecture,[],[f15])).
% 1.80/0.60  fof(f15,conjecture,(
% 1.80/0.60    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.80/0.60  fof(f51,plain,(
% 1.80/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f32])).
% 1.80/0.60  fof(f55,plain,(
% 1.80/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.80/0.60    inference(definition_unfolding,[],[f43,f42])).
% 1.80/0.60  fof(f43,plain,(
% 1.80/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.80/0.60    inference(cnf_transformation,[],[f11])).
% 1.80/0.60  fof(f11,axiom,(
% 1.80/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.80/0.60  fof(f1029,plain,(
% 1.80/0.60    sK3 = k4_xboole_0(sK0,sK2)),
% 1.80/0.60    inference(forward_demodulation,[],[f1024,f760])).
% 1.80/0.60  fof(f760,plain,(
% 1.80/0.60    sK3 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 1.80/0.60    inference(backward_demodulation,[],[f604,f759])).
% 1.80/0.60  fof(f759,plain,(
% 1.80/0.60    sK3 = k4_xboole_0(sK3,sK2)),
% 1.80/0.60    inference(forward_demodulation,[],[f754,f38])).
% 1.80/0.60  fof(f754,plain,(
% 1.80/0.60    k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,sK2)),
% 1.80/0.60    inference(superposition,[],[f454,f740])).
% 1.80/0.60  fof(f740,plain,(
% 1.80/0.60    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 1.80/0.60    inference(superposition,[],[f737,f340])).
% 1.80/0.60  fof(f340,plain,(
% 1.80/0.60    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0)) )),
% 1.80/0.60    inference(superposition,[],[f52,f317])).
% 1.80/0.60  fof(f317,plain,(
% 1.80/0.60    sK2 = k4_xboole_0(sK2,sK0)),
% 1.80/0.60    inference(forward_demodulation,[],[f292,f38])).
% 1.80/0.60  fof(f292,plain,(
% 1.80/0.60    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0)),
% 1.80/0.60    inference(superposition,[],[f55,f123])).
% 1.80/0.60  fof(f123,plain,(
% 1.80/0.60    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 1.80/0.60    inference(resolution,[],[f121,f39])).
% 1.80/0.60  fof(f121,plain,(
% 1.80/0.60    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)))) )),
% 1.80/0.60    inference(resolution,[],[f57,f34])).
% 1.80/0.60  fof(f52,plain,(
% 1.80/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.80/0.60    inference(cnf_transformation,[],[f10])).
% 1.80/0.60  fof(f10,axiom,(
% 1.80/0.60    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.80/0.60  fof(f737,plain,(
% 1.80/0.60    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 1.80/0.60    inference(forward_demodulation,[],[f734,f175])).
% 1.80/0.60  fof(f175,plain,(
% 1.80/0.60    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 1.80/0.60    inference(forward_demodulation,[],[f162,f44])).
% 1.80/0.60  fof(f44,plain,(
% 1.80/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.80/0.60    inference(cnf_transformation,[],[f7])).
% 1.80/0.60  fof(f7,axiom,(
% 1.80/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.80/0.60  fof(f162,plain,(
% 1.80/0.60    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 1.80/0.60    inference(superposition,[],[f52,f59])).
% 1.80/0.60  fof(f59,plain,(
% 1.80/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.80/0.60    inference(backward_demodulation,[],[f54,f38])).
% 1.80/0.60  fof(f54,plain,(
% 1.80/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.80/0.60    inference(definition_unfolding,[],[f37,f42])).
% 1.80/0.60  fof(f37,plain,(
% 1.80/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f6])).
% 1.80/0.60  fof(f6,axiom,(
% 1.80/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.80/0.60  fof(f734,plain,(
% 1.80/0.60    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k2_xboole_0(sK1,sK2))),
% 1.80/0.60    inference(superposition,[],[f340,f482])).
% 1.80/0.60  fof(f482,plain,(
% 1.80/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.80/0.60    inference(superposition,[],[f373,f53])).
% 1.80/0.60  fof(f53,plain,(
% 1.80/0.60    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.80/0.60    inference(cnf_transformation,[],[f13])).
% 1.80/0.60  fof(f13,axiom,(
% 1.80/0.60    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 1.80/0.60  fof(f373,plain,(
% 1.80/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 1.80/0.60    inference(superposition,[],[f324,f33])).
% 1.80/0.60  fof(f33,plain,(
% 1.80/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.80/0.60    inference(cnf_transformation,[],[f26])).
% 1.80/0.60  fof(f324,plain,(
% 1.80/0.60    ( ! [X2] : (k2_xboole_0(sK2,X2) = k2_xboole_0(k2_xboole_0(sK2,X2),sK2)) )),
% 1.80/0.60    inference(backward_demodulation,[],[f263,f317])).
% 1.80/0.60  fof(f263,plain,(
% 1.80/0.60    ( ! [X2] : (k2_xboole_0(k4_xboole_0(sK2,sK0),X2) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK0),X2),sK2)) )),
% 1.80/0.60    inference(forward_demodulation,[],[f262,f62])).
% 1.80/0.60  fof(f62,plain,(
% 1.80/0.60    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.80/0.60    inference(superposition,[],[f61,f41])).
% 1.80/0.60  fof(f41,plain,(
% 1.80/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f1])).
% 1.80/0.60  fof(f1,axiom,(
% 1.80/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.80/0.60  fof(f61,plain,(
% 1.80/0.60    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 1.80/0.60    inference(forward_demodulation,[],[f60,f40])).
% 1.80/0.60  fof(f40,plain,(
% 1.80/0.60    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.80/0.60    inference(cnf_transformation,[],[f17])).
% 1.80/0.60  fof(f17,plain,(
% 1.80/0.60    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.80/0.60    inference(rectify,[],[f2])).
% 1.80/0.60  fof(f2,axiom,(
% 1.80/0.60    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.80/0.60  fof(f60,plain,(
% 1.80/0.60    ( ! [X1] : (k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0)) )),
% 1.80/0.60    inference(superposition,[],[f44,f59])).
% 1.80/0.60  fof(f262,plain,(
% 1.80/0.60    ( ! [X2] : (k2_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK0),X2),sK2) = k2_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK2,sK0),X2))) )),
% 1.80/0.60    inference(forward_demodulation,[],[f259,f41])).
% 1.80/0.60  fof(f259,plain,(
% 1.80/0.60    ( ! [X2] : (k2_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK0),X2),sK2) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK0),X2),k1_xboole_0)) )),
% 1.80/0.60    inference(superposition,[],[f44,f171])).
% 1.80/0.60  fof(f171,plain,(
% 1.80/0.60    ( ! [X12] : (k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X12))) )),
% 1.80/0.60    inference(forward_demodulation,[],[f158,f82])).
% 1.80/0.60  fof(f82,plain,(
% 1.80/0.60    ( ! [X8] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X8)) )),
% 1.80/0.60    inference(forward_demodulation,[],[f78,f59])).
% 1.80/0.60  fof(f78,plain,(
% 1.80/0.60    ( ! [X8] : (k4_xboole_0(k1_xboole_0,X8) = k4_xboole_0(X8,X8)) )),
% 1.80/0.60    inference(superposition,[],[f45,f62])).
% 1.80/0.60  fof(f45,plain,(
% 1.80/0.60    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f9])).
% 1.80/0.60  fof(f9,axiom,(
% 1.80/0.60    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.80/0.60  fof(f158,plain,(
% 1.80/0.60    ( ! [X12] : (k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X12)) = k4_xboole_0(k1_xboole_0,X12)) )),
% 1.80/0.60    inference(superposition,[],[f52,f123])).
% 1.80/0.60  fof(f454,plain,(
% 1.80/0.60    ( ! [X2] : (k4_xboole_0(sK3,k4_xboole_0(X2,sK1)) = k4_xboole_0(sK3,X2)) )),
% 1.80/0.60    inference(forward_demodulation,[],[f448,f343])).
% 1.80/0.60  fof(f343,plain,(
% 1.80/0.60    ( ! [X0] : (k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0)) )),
% 1.80/0.60    inference(superposition,[],[f52,f325])).
% 1.80/0.60  fof(f325,plain,(
% 1.80/0.60    sK3 = k4_xboole_0(sK3,sK1)),
% 1.80/0.60    inference(forward_demodulation,[],[f293,f38])).
% 1.80/0.60  fof(f293,plain,(
% 1.80/0.60    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0)),
% 1.80/0.60    inference(superposition,[],[f55,f141])).
% 1.80/0.60  fof(f141,plain,(
% 1.80/0.60    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 1.80/0.60    inference(resolution,[],[f122,f39])).
% 1.80/0.60  fof(f122,plain,(
% 1.80/0.60    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)))) )),
% 1.80/0.60    inference(resolution,[],[f57,f35])).
% 1.80/0.60  fof(f35,plain,(
% 1.80/0.60    r1_xboole_0(sK3,sK1)),
% 1.80/0.60    inference(cnf_transformation,[],[f26])).
% 1.80/0.60  fof(f448,plain,(
% 1.80/0.60    ( ! [X2] : (k4_xboole_0(sK3,k4_xboole_0(X2,sK1)) = k4_xboole_0(sK3,k2_xboole_0(sK1,X2))) )),
% 1.80/0.60    inference(superposition,[],[f343,f44])).
% 1.80/0.60  fof(f604,plain,(
% 1.80/0.60    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k4_xboole_0(sK3,sK2)),
% 1.80/0.60    inference(superposition,[],[f45,f598])).
% 1.80/0.60  fof(f598,plain,(
% 1.80/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2)),
% 1.80/0.60    inference(forward_demodulation,[],[f597,f89])).
% 1.80/0.60  fof(f89,plain,(
% 1.80/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.80/0.60    inference(forward_demodulation,[],[f88,f33])).
% 1.80/0.60  fof(f88,plain,(
% 1.80/0.60    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.80/0.60    inference(forward_demodulation,[],[f87,f41])).
% 1.80/0.60  fof(f87,plain,(
% 1.80/0.60    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.80/0.60    inference(forward_demodulation,[],[f86,f44])).
% 1.80/0.60  fof(f86,plain,(
% 1.80/0.60    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3))),
% 1.80/0.60    inference(superposition,[],[f44,f74])).
% 1.80/0.60  fof(f74,plain,(
% 1.80/0.60    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 1.80/0.60    inference(superposition,[],[f45,f33])).
% 1.80/0.60  fof(f597,plain,(
% 1.80/0.60    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.80/0.60    inference(superposition,[],[f44,f578])).
% 1.80/0.60  fof(f578,plain,(
% 1.80/0.60    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 1.80/0.60    inference(backward_demodulation,[],[f74,f575])).
% 1.80/0.60  fof(f575,plain,(
% 1.80/0.60    sK2 = k4_xboole_0(sK2,sK3)),
% 1.80/0.60    inference(forward_demodulation,[],[f570,f38])).
% 1.80/0.60  fof(f570,plain,(
% 1.80/0.60    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k1_xboole_0)),
% 1.80/0.60    inference(superposition,[],[f440,f559])).
% 1.80/0.60  fof(f559,plain,(
% 1.80/0.60    k1_xboole_0 = k4_xboole_0(sK3,sK0)),
% 1.80/0.60    inference(superposition,[],[f445,f91])).
% 1.80/0.60  fof(f91,plain,(
% 1.80/0.60    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.80/0.60    inference(forward_demodulation,[],[f90,f59])).
% 1.80/0.60  fof(f90,plain,(
% 1.80/0.60    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 1.80/0.60    inference(superposition,[],[f45,f89])).
% 1.80/0.60  fof(f445,plain,(
% 1.80/0.60    ( ! [X0] : (k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK1))) )),
% 1.80/0.60    inference(superposition,[],[f343,f41])).
% 1.80/0.60  fof(f440,plain,(
% 1.80/0.60    ( ! [X2] : (k4_xboole_0(sK2,k4_xboole_0(X2,sK0)) = k4_xboole_0(sK2,X2)) )),
% 1.80/0.60    inference(forward_demodulation,[],[f434,f340])).
% 1.80/0.60  fof(f434,plain,(
% 1.80/0.60    ( ! [X2] : (k4_xboole_0(sK2,k4_xboole_0(X2,sK0)) = k4_xboole_0(sK2,k2_xboole_0(sK0,X2))) )),
% 1.80/0.60    inference(superposition,[],[f340,f44])).
% 1.80/0.60  fof(f1024,plain,(
% 1.80/0.60    k4_xboole_0(sK0,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 1.80/0.60    inference(superposition,[],[f45,f995])).
% 1.80/0.60  fof(f995,plain,(
% 1.80/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK2)),
% 1.80/0.60    inference(superposition,[],[f992,f41])).
% 1.80/0.60  fof(f992,plain,(
% 1.80/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK0)),
% 1.80/0.60    inference(forward_demodulation,[],[f982,f85])).
% 1.80/0.60  fof(f85,plain,(
% 1.80/0.60    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X2,k2_xboole_0(X1,X2))) )),
% 1.80/0.60    inference(forward_demodulation,[],[f81,f44])).
% 1.80/0.60  fof(f81,plain,(
% 1.80/0.60    ( ! [X2,X1] : (k2_xboole_0(X2,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k4_xboole_0(X1,X2))) )),
% 1.80/0.60    inference(superposition,[],[f44,f45])).
% 1.80/0.60  fof(f982,plain,(
% 1.80/0.60    k2_xboole_0(sK2,sK0) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK0))),
% 1.80/0.60    inference(superposition,[],[f221,f969])).
% 1.80/0.60  fof(f969,plain,(
% 1.80/0.60    sK0 = k2_xboole_0(sK3,sK0)),
% 1.80/0.60    inference(superposition,[],[f518,f583])).
% 1.80/0.60  fof(f583,plain,(
% 1.80/0.60    sK0 = k2_xboole_0(sK0,sK3)),
% 1.80/0.60    inference(forward_demodulation,[],[f582,f62])).
% 1.80/0.60  fof(f582,plain,(
% 1.80/0.60    k2_xboole_0(sK0,sK3) = k2_xboole_0(k1_xboole_0,sK0)),
% 1.80/0.60    inference(forward_demodulation,[],[f574,f41])).
% 1.80/0.60  fof(f574,plain,(
% 1.80/0.60    k2_xboole_0(sK0,sK3) = k2_xboole_0(sK0,k1_xboole_0)),
% 1.80/0.60    inference(superposition,[],[f44,f559])).
% 1.80/0.60  fof(f518,plain,(
% 1.80/0.60    ( ! [X2] : (k2_xboole_0(X2,sK3) = k2_xboole_0(sK3,k2_xboole_0(X2,sK3))) )),
% 1.80/0.60    inference(superposition,[],[f419,f41])).
% 1.80/0.60  fof(f419,plain,(
% 1.80/0.60    ( ! [X0] : (k2_xboole_0(X0,sK3) = k2_xboole_0(k2_xboole_0(X0,sK3),sK3)) )),
% 1.80/0.60    inference(superposition,[],[f332,f41])).
% 1.80/0.60  fof(f332,plain,(
% 1.80/0.60    ( ! [X2] : (k2_xboole_0(sK3,X2) = k2_xboole_0(k2_xboole_0(sK3,X2),sK3)) )),
% 1.80/0.60    inference(backward_demodulation,[],[f275,f325])).
% 1.80/0.60  fof(f275,plain,(
% 1.80/0.60    ( ! [X2] : (k2_xboole_0(k4_xboole_0(sK3,sK1),X2) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK3,sK1),X2),sK3)) )),
% 1.80/0.60    inference(forward_demodulation,[],[f274,f62])).
% 1.80/0.60  fof(f274,plain,(
% 1.80/0.60    ( ! [X2] : (k2_xboole_0(k2_xboole_0(k4_xboole_0(sK3,sK1),X2),sK3) = k2_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK3,sK1),X2))) )),
% 1.80/0.60    inference(forward_demodulation,[],[f271,f41])).
% 1.80/0.60  fof(f271,plain,(
% 1.80/0.60    ( ! [X2] : (k2_xboole_0(k2_xboole_0(k4_xboole_0(sK3,sK1),X2),sK3) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK3,sK1),X2),k1_xboole_0)) )),
% 1.80/0.60    inference(superposition,[],[f44,f174])).
% 1.80/0.60  fof(f174,plain,(
% 1.80/0.60    ( ! [X14] : (k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X14))) )),
% 1.80/0.60    inference(forward_demodulation,[],[f160,f82])).
% 1.80/0.60  fof(f160,plain,(
% 1.80/0.60    ( ! [X14] : (k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X14)) = k4_xboole_0(k1_xboole_0,X14)) )),
% 1.80/0.60    inference(superposition,[],[f52,f141])).
% 1.80/0.60  fof(f221,plain,(
% 1.80/0.60    ( ! [X19] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X19)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X19))) )),
% 1.80/0.60    inference(forward_demodulation,[],[f205,f53])).
% 1.80/0.60  fof(f205,plain,(
% 1.80/0.60    ( ! [X19] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X19)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X19)) )),
% 1.80/0.60    inference(superposition,[],[f53,f33])).
% 1.80/0.60  fof(f313,plain,(
% 1.80/0.60    sK1 = k4_xboole_0(sK1,sK3)),
% 1.80/0.60    inference(forward_demodulation,[],[f291,f38])).
% 1.80/0.60  fof(f291,plain,(
% 1.80/0.60    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0)),
% 1.80/0.60    inference(superposition,[],[f55,f231])).
% 1.80/0.60  fof(f231,plain,(
% 1.80/0.60    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.80/0.60    inference(resolution,[],[f229,f39])).
% 1.80/0.60  fof(f229,plain,(
% 1.80/0.60    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))) )),
% 1.80/0.60    inference(resolution,[],[f197,f57])).
% 1.80/0.60  fof(f197,plain,(
% 1.80/0.60    r1_xboole_0(sK1,sK3)),
% 1.80/0.60    inference(duplicate_literal_removal,[],[f196])).
% 1.80/0.60  fof(f196,plain,(
% 1.80/0.60    r1_xboole_0(sK1,sK3) | r1_xboole_0(sK1,sK3)),
% 1.80/0.60    inference(resolution,[],[f108,f49])).
% 1.80/0.60  fof(f108,plain,(
% 1.80/0.60    ( ! [X1] : (~r2_hidden(sK6(X1,sK3),sK1) | r1_xboole_0(X1,sK3)) )),
% 1.80/0.60    inference(resolution,[],[f93,f50])).
% 1.80/0.60  fof(f93,plain,(
% 1.80/0.60    ( ! [X1] : (~r2_hidden(X1,sK3) | ~r2_hidden(X1,sK1)) )),
% 1.80/0.60    inference(resolution,[],[f51,f35])).
% 1.80/0.60  fof(f1010,plain,(
% 1.80/0.60    sK2 = k4_xboole_0(sK1,sK0)),
% 1.80/0.60    inference(forward_demodulation,[],[f1009,f317])).
% 1.80/0.60  fof(f1009,plain,(
% 1.80/0.60    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK1,sK0)),
% 1.80/0.60    inference(forward_demodulation,[],[f1003,f75])).
% 1.80/0.60  fof(f75,plain,(
% 1.80/0.60    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 1.80/0.60    inference(superposition,[],[f45,f41])).
% 1.80/0.60  fof(f1003,plain,(
% 1.80/0.60    k4_xboole_0(sK2,sK0) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0)),
% 1.80/0.60    inference(superposition,[],[f45,f992])).
% 1.80/0.60  fof(f36,plain,(
% 1.80/0.60    sK1 != sK2),
% 1.80/0.60    inference(cnf_transformation,[],[f26])).
% 1.80/0.60  % SZS output end Proof for theBenchmark
% 1.80/0.60  % (22574)------------------------------
% 1.80/0.60  % (22574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.60  % (22574)Termination reason: Refutation
% 1.80/0.60  
% 1.80/0.60  % (22574)Memory used [KB]: 6908
% 1.80/0.60  % (22574)Time elapsed: 0.170 s
% 1.80/0.60  % (22574)------------------------------
% 1.80/0.60  % (22574)------------------------------
% 1.80/0.61  % (22561)Success in time 0.253 s
%------------------------------------------------------------------------------
