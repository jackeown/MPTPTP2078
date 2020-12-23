%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:29 EST 2020

% Result     : Theorem 6.51s
% Output     : Refutation 6.51s
% Verified   : 
% Statistics : Number of formulae       :  164 (100532 expanded)
%              Number of leaves         :   25 (34970 expanded)
%              Depth                    :   42
%              Number of atoms          :  308 (105016 expanded)
%              Number of equality atoms :  259 (104967 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3182,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3163,f117])).

fof(f117,plain,(
    ~ r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f38,f99])).

fof(f99,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f46,f76])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f69,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f53,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f55,f54])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f69,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f38,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f3163,plain,(
    r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f101,f3134])).

fof(f3134,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(forward_demodulation,[],[f3133,f2979])).

fof(f2979,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,X0,X1,X2),k1_xboole_0) = k6_enumset1(sK0,X0,X1,X2,sK0,sK0,sK0,sK0) ),
    inference(backward_demodulation,[],[f2618,f2978])).

fof(f2978,plain,(
    ! [X12,X13,X11] : k6_enumset1(sK0,X11,X12,X13,sK1,sK0,sK0,sK0) = k6_enumset1(sK0,X11,X12,X13,sK0,sK0,sK0,sK0) ),
    inference(backward_demodulation,[],[f2626,f2977])).

fof(f2977,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X0,X1,X2,sK1),k1_xboole_0) = k6_enumset1(sK0,X0,X1,X2,sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f2961,f1380])).

fof(f1380,plain,(
    ! [X4,X2,X5,X3] : k1_xboole_0 = k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5),k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5)) ),
    inference(backward_demodulation,[],[f1378,f1379])).

fof(f1379,plain,(
    ! [X6,X8,X7,X9] : k6_enumset1(X6,X6,X6,X6,X6,X7,X8,X9) = k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X7,X8,X9),k6_enumset1(X6,X7,X8,X9,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f1216,f1277])).

fof(f1277,plain,(
    ! [X6,X4,X7,X5] : k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X5,X6,X7,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X4,X4,X4,X4,X5,X6,X7,sK1)))) = k6_enumset1(X4,X5,X6,X7,sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f1231,f78])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)))) ),
    inference(definition_unfolding,[],[f42,f70,f73,f73])).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f44,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(f1231,plain,(
    ! [X6,X4,X7,X5] : k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X5,X6,X7,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X4,X4,X4,X4,X5,X6,X7,sK1)))) = k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7)))) ),
    inference(backward_demodulation,[],[f208,f1225])).

fof(f1225,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f1224,f58])).

fof(f58,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f1224,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f1223,f197])).

fof(f197,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK0,sK0,sK0,sK0) = k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(backward_demodulation,[],[f195,f196])).

fof(f196,plain,(
    k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK1,sK1,sK1,sK0,sK0,sK0,sK0,sK0) ),
    inference(backward_demodulation,[],[f194,f189])).

fof(f189,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[],[f82,f171])).

fof(f171,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f170,f83])).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f45,f70])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f170,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f167,f58])).

fof(f167,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)) ),
    inference(superposition,[],[f141,f88])).

fof(f88,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(definition_unfolding,[],[f59,f57,f70])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f141,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0))) ),
    inference(forward_demodulation,[],[f140,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f140,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) ),
    inference(superposition,[],[f56,f107])).

fof(f107,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f79,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f79,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f37,f76,f70,f76,f76])).

fof(f37,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f43,f70,f76,f54])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

fof(f194,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k6_enumset1(sK1,sK1,sK1,sK0,sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f188,f78])).

fof(f188,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) ),
    inference(superposition,[],[f80,f171])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)))) ),
    inference(definition_unfolding,[],[f40,f77,f70,f73,f72])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)))) ),
    inference(definition_unfolding,[],[f39,f70,f72,f73])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l142_enumset1)).

fof(f195,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK0,sK0,sK0,sK0) = k6_enumset1(sK1,sK1,sK1,sK0,sK0,sK0,sK0,sK0) ),
    inference(backward_demodulation,[],[f187,f194])).

fof(f187,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f78,f171])).

fof(f1223,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f1222,f78])).

fof(f1222,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f1221,f616])).

fof(f616,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(backward_demodulation,[],[f603,f604])).

fof(f604,plain,(
    ! [X2] : k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,sK1,sK1,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f83,f204])).

fof(f204,plain,(
    ! [X0] : k6_enumset1(X0,sK1,sK1,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(superposition,[],[f82,f196])).

fof(f603,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,sK1,sK1,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f88,f204])).

fof(f1221,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f1198,f897])).

fof(f897,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) ),
    inference(backward_demodulation,[],[f542,f894])).

fof(f894,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) ),
    inference(superposition,[],[f56,f847])).

fof(f847,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f826,f58])).

fof(f826,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f413,f384])).

fof(f384,plain,(
    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(backward_demodulation,[],[f382,f383])).

fof(f383,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))) ),
    inference(forward_demodulation,[],[f377,f60])).

fof(f377,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) ),
    inference(superposition,[],[f83,f203])).

fof(f203,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) ),
    inference(forward_demodulation,[],[f193,f56])).

fof(f193,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0) ),
    inference(superposition,[],[f56,f171])).

fof(f382,plain,(
    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))))) ),
    inference(forward_demodulation,[],[f376,f60])).

fof(f376,plain,(
    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) ),
    inference(superposition,[],[f88,f203])).

fof(f413,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) ),
    inference(superposition,[],[f56,f384])).

fof(f542,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) ),
    inference(superposition,[],[f253,f305])).

fof(f305,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))) ),
    inference(forward_demodulation,[],[f304,f56])).

fof(f304,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) ),
    inference(superposition,[],[f56,f189])).

fof(f253,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f56,f241])).

fof(f241,plain,(
    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(backward_demodulation,[],[f201,f235])).

fof(f235,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f202,f60])).

fof(f202,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f192,f189])).

fof(f192,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f83,f171])).

fof(f201,plain,(
    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f200,f60])).

fof(f200,plain,(
    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f191,f189])).

fof(f191,plain,(
    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) ),
    inference(superposition,[],[f88,f171])).

fof(f1198,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f208,f235])).

fof(f208,plain,(
    ! [X6,X4,X7,X5] : k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X5,X6,X7,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X4,X4,X4,X4,X5,X6,X7,sK1)))) = k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7)))) ),
    inference(superposition,[],[f80,f197])).

fof(f1216,plain,(
    ! [X6,X8,X7,X9] : k6_enumset1(X6,X6,X6,X6,X6,X7,X8,X9) = k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X7,X8,X9),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X7,X8,X9,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X6,X6,X6,X6,X7,X8,X9,sK1))))) ),
    inference(superposition,[],[f83,f208])).

fof(f1378,plain,(
    ! [X4,X2,X5,X3] : k1_xboole_0 = k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5),k6_enumset1(X2,X3,X4,X5,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f1215,f1277])).

fof(f1215,plain,(
    ! [X4,X2,X5,X3] : k1_xboole_0 = k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X3,X4,X5,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X2,X2,X2,X2,X3,X4,X5,sK1)))))) ),
    inference(superposition,[],[f88,f208])).

fof(f2961,plain,(
    ! [X2,X0,X1] : k6_enumset1(sK0,X0,X1,X2,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X0,X1,X2,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f1277,f1334])).

fof(f1334,plain,(
    ! [X10,X8,X11,X9] : k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,X8,X9,X10,X11)) ),
    inference(forward_demodulation,[],[f1254,f1278])).

fof(f1278,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(sK0,sK0,sK0,sK0,X0,X1,X2,X3) = k6_enumset1(sK1,sK0,sK0,sK0,X0,X1,X2,X3) ),
    inference(forward_demodulation,[],[f1232,f78])).

fof(f1232,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(sK1,sK0,sK0,sK0,X0,X1,X2,X3) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(backward_demodulation,[],[f212,f1225])).

fof(f212,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k6_enumset1(sK1,sK0,sK0,sK0,X0,X1,X2,X3) ),
    inference(forward_demodulation,[],[f207,f82])).

fof(f207,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X0,X1,X2,X3),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X0,X1,X2,X3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f81,f197])).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f41,f77,f70,f76])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).

fof(f1254,plain,(
    ! [X10,X8,X11,X9] : k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK0,sK0,sK0,X8,X9,X10,X11)) ),
    inference(backward_demodulation,[],[f770,f1225])).

fof(f770,plain,(
    ! [X10,X8,X11,X9] : k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK0,sK0,sK0,X8,X9,X10,X11)) ),
    inference(superposition,[],[f83,f212])).

fof(f2626,plain,(
    ! [X12,X13,X11] : k6_enumset1(sK0,X11,X12,X13,sK1,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X11,X12,X13,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f2625,f1380])).

fof(f2625,plain,(
    ! [X12,X13,X11] : k6_enumset1(sK0,X11,X12,X13,sK1,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X11,X12,X13,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f2624,f1281])).

fof(f1281,plain,(
    ! [X19,X17,X20,X18] : k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,X17,X18,X19,X20)) ),
    inference(backward_demodulation,[],[f802,f1278])).

fof(f802,plain,(
    ! [X19,X17,X20,X18] : k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k6_enumset1(sK1,sK0,sK0,sK0,X17,X18,X19,X20)) ),
    inference(superposition,[],[f83,f213])).

fof(f213,plain,(
    ! [X10,X8,X11,X9] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X8,X9,X10,X11),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X8,X9,X10,X11),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0)))) = k6_enumset1(sK1,sK0,sK0,sK0,X8,X9,X10,X11) ),
    inference(forward_demodulation,[],[f209,f212])).

fof(f209,plain,(
    ! [X10,X8,X11,X9] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X8,X9,X10,X11),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X8,X9,X10,X11),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0)))) = k5_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X9,X10,X11),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X9,X10,X11),k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f80,f197])).

fof(f2624,plain,(
    ! [X12,X13,X11] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X11,X12,X13,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,X11,X12,X13,sK1)))) = k6_enumset1(sK0,X11,X12,X13,sK1,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f2623,f2618])).

fof(f2623,plain,(
    ! [X12,X13,X11] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X11,X12,X13,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,X11,X12,X13,sK1)))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,X11,X12,X13),k1_xboole_0) ),
    inference(forward_demodulation,[],[f2610,f1380])).

fof(f2610,plain,(
    ! [X12,X13,X11] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X11,X12,X13,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,X11,X12,X13,sK1)))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,X11,X12,X13),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0))) ),
    inference(superposition,[],[f80,f1281])).

fof(f2618,plain,(
    ! [X2,X0,X1] : k6_enumset1(sK0,X0,X1,X2,sK1,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,X0,X1,X2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f2607,f1380])).

fof(f2607,plain,(
    ! [X2,X0,X1] : k6_enumset1(sK0,X0,X1,X2,sK1,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,X0,X1,X2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0))) ),
    inference(superposition,[],[f78,f1281])).

fof(f3133,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3104,f1380])).

fof(f3104,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(superposition,[],[f78,f1359])).

fof(f1359,plain,(
    ! [X21,X19,X22,X20] : k6_enumset1(X19,X19,X19,X19,X20,X21,X22,sK1) = k3_xboole_0(k6_enumset1(X19,X19,X19,X19,X20,X21,X22,sK1),k6_enumset1(X19,X20,X21,X22,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f1358,f78])).

fof(f1358,plain,(
    ! [X21,X19,X22,X20] : k6_enumset1(X19,X19,X19,X19,X20,X21,X22,sK1) = k3_xboole_0(k6_enumset1(X19,X19,X19,X19,X20,X21,X22,sK1),k5_xboole_0(k6_enumset1(X19,X19,X19,X19,X19,X20,X21,X22),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X19,X19,X19,X19,X19,X20,X21,X22))))) ),
    inference(forward_demodulation,[],[f1208,f1225])).

fof(f1208,plain,(
    ! [X21,X19,X22,X20] : k6_enumset1(X19,X19,X19,X19,X20,X21,X22,sK1) = k3_xboole_0(k6_enumset1(X19,X19,X19,X19,X20,X21,X22,sK1),k5_xboole_0(k6_enumset1(X19,X19,X19,X19,X19,X20,X21,X22),k5_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X19,X19,X19,X19,X19,X20,X21,X22))))) ),
    inference(superposition,[],[f83,f208])).

fof(f101,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f64,f74])).

fof(f64,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).

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
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:38:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (5493)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (5501)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (5502)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (5507)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.56  % (5491)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (5491)Refutation not found, incomplete strategy% (5491)------------------------------
% 0.22/0.56  % (5491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (5491)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (5491)Memory used [KB]: 10618
% 0.22/0.56  % (5491)Time elapsed: 0.125 s
% 0.22/0.56  % (5491)------------------------------
% 0.22/0.56  % (5491)------------------------------
% 0.22/0.56  % (5495)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (5495)Refutation not found, incomplete strategy% (5495)------------------------------
% 0.22/0.56  % (5495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (5486)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.56  % (5495)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (5495)Memory used [KB]: 10618
% 0.22/0.56  % (5495)Time elapsed: 0.128 s
% 0.22/0.56  % (5495)------------------------------
% 0.22/0.56  % (5495)------------------------------
% 0.22/0.56  % (5499)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (5487)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.58  % (5494)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.58  % (5503)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.58  % (5506)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.58  % (5481)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.59  % (5488)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.59  % (5482)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.59  % (5484)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.59  % (5480)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.59  % (5480)Refutation not found, incomplete strategy% (5480)------------------------------
% 0.22/0.59  % (5480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (5480)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (5480)Memory used [KB]: 1663
% 0.22/0.59  % (5480)Time elapsed: 0.144 s
% 0.22/0.59  % (5480)------------------------------
% 0.22/0.59  % (5480)------------------------------
% 1.80/0.60  % (5505)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.80/0.60  % (5479)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.80/0.60  % (5489)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.80/0.60  % (5483)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.80/0.60  % (5506)Refutation not found, incomplete strategy% (5506)------------------------------
% 1.80/0.60  % (5506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.60  % (5506)Termination reason: Refutation not found, incomplete strategy
% 1.80/0.60  
% 1.80/0.60  % (5506)Memory used [KB]: 6140
% 1.80/0.60  % (5506)Time elapsed: 0.175 s
% 1.80/0.60  % (5506)------------------------------
% 1.80/0.60  % (5506)------------------------------
% 1.80/0.60  % (5492)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.80/0.60  % (5504)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.80/0.60  % (5497)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.80/0.61  % (5508)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.80/0.61  % (5496)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.80/0.61  % (5490)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.80/0.61  % (5500)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.80/0.61  % (5504)Refutation not found, incomplete strategy% (5504)------------------------------
% 1.80/0.61  % (5504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.61  % (5498)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.80/0.61  % (5497)Refutation not found, incomplete strategy% (5497)------------------------------
% 1.80/0.61  % (5497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.61  % (5485)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.91/0.62  % (5505)Refutation not found, incomplete strategy% (5505)------------------------------
% 1.91/0.62  % (5505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.62  % (5504)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.62  
% 1.91/0.62  % (5504)Memory used [KB]: 6140
% 1.91/0.62  % (5504)Time elapsed: 0.163 s
% 1.91/0.62  % (5504)------------------------------
% 1.91/0.62  % (5504)------------------------------
% 1.91/0.62  % (5497)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.62  
% 1.91/0.62  % (5497)Memory used [KB]: 1663
% 1.91/0.62  % (5497)Time elapsed: 0.187 s
% 1.91/0.62  % (5497)------------------------------
% 1.91/0.62  % (5497)------------------------------
% 1.91/0.62  % (5505)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.62  
% 1.91/0.62  % (5505)Memory used [KB]: 6140
% 1.91/0.62  % (5505)Time elapsed: 0.201 s
% 1.91/0.62  % (5505)------------------------------
% 1.91/0.62  % (5505)------------------------------
% 2.04/0.63  % (5508)Refutation not found, incomplete strategy% (5508)------------------------------
% 2.04/0.63  % (5508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.63  % (5508)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.63  
% 2.04/0.63  % (5508)Memory used [KB]: 1663
% 2.04/0.63  % (5508)Time elapsed: 0.003 s
% 2.04/0.63  % (5508)------------------------------
% 2.04/0.63  % (5508)------------------------------
% 2.04/0.68  % (5510)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.04/0.69  % (5511)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.60/0.71  % (5494)Refutation not found, incomplete strategy% (5494)------------------------------
% 2.60/0.71  % (5494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.60/0.71  % (5494)Termination reason: Refutation not found, incomplete strategy
% 2.60/0.71  
% 2.60/0.71  % (5494)Memory used [KB]: 6140
% 2.60/0.71  % (5494)Time elapsed: 0.277 s
% 2.60/0.71  % (5494)------------------------------
% 2.60/0.71  % (5494)------------------------------
% 2.60/0.72  % (5515)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.60/0.72  % (5515)Refutation not found, incomplete strategy% (5515)------------------------------
% 2.60/0.72  % (5515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.60/0.72  % (5515)Termination reason: Refutation not found, incomplete strategy
% 2.60/0.72  
% 2.60/0.72  % (5515)Memory used [KB]: 6140
% 2.60/0.72  % (5515)Time elapsed: 0.102 s
% 2.60/0.72  % (5515)------------------------------
% 2.60/0.72  % (5515)------------------------------
% 2.60/0.73  % (5482)Refutation not found, incomplete strategy% (5482)------------------------------
% 2.60/0.73  % (5482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.60/0.73  % (5482)Termination reason: Refutation not found, incomplete strategy
% 2.60/0.73  
% 2.60/0.73  % (5482)Memory used [KB]: 6140
% 2.60/0.73  % (5482)Time elapsed: 0.272 s
% 2.60/0.73  % (5482)------------------------------
% 2.60/0.73  % (5482)------------------------------
% 2.60/0.74  % (5530)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.60/0.75  % (5479)Refutation not found, incomplete strategy% (5479)------------------------------
% 2.60/0.75  % (5479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.60/0.75  % (5518)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.60/0.75  % (5527)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.60/0.75  % (5528)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.60/0.76  % (5479)Termination reason: Refutation not found, incomplete strategy
% 2.60/0.76  
% 2.60/0.76  % (5479)Memory used [KB]: 1663
% 2.60/0.76  % (5479)Time elapsed: 0.324 s
% 2.60/0.76  % (5479)------------------------------
% 2.60/0.76  % (5479)------------------------------
% 2.60/0.76  % (5533)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 3.09/0.84  % (5503)Time limit reached!
% 3.09/0.84  % (5503)------------------------------
% 3.09/0.84  % (5503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.09/0.85  % (5481)Time limit reached!
% 3.09/0.85  % (5481)------------------------------
% 3.09/0.85  % (5481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.09/0.85  % (5481)Termination reason: Time limit
% 3.09/0.85  
% 3.09/0.85  % (5481)Memory used [KB]: 6780
% 3.09/0.85  % (5481)Time elapsed: 0.424 s
% 3.09/0.85  % (5481)------------------------------
% 3.09/0.85  % (5481)------------------------------
% 3.09/0.86  % (5503)Termination reason: Time limit
% 3.09/0.86  % (5503)Termination phase: Saturation
% 3.09/0.86  
% 3.09/0.86  % (5503)Memory used [KB]: 13688
% 3.09/0.86  % (5503)Time elapsed: 0.400 s
% 3.09/0.86  % (5503)------------------------------
% 3.09/0.86  % (5503)------------------------------
% 3.09/0.86  % (5573)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 3.58/0.87  % (5589)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 3.58/0.87  % (5593)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 3.58/0.87  % (5598)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 3.85/0.94  % (5485)Time limit reached!
% 3.85/0.94  % (5485)------------------------------
% 3.85/0.94  % (5485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.85/0.95  % (5661)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 3.85/0.95  % (5493)Time limit reached!
% 3.85/0.95  % (5493)------------------------------
% 3.85/0.95  % (5493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.85/0.95  % (5493)Termination reason: Time limit
% 3.85/0.95  
% 3.85/0.95  % (5493)Memory used [KB]: 6140
% 3.85/0.95  % (5493)Time elapsed: 0.508 s
% 3.85/0.95  % (5493)------------------------------
% 3.85/0.95  % (5493)------------------------------
% 3.85/0.96  % (5485)Termination reason: Time limit
% 3.85/0.96  % (5485)Termination phase: Saturation
% 3.85/0.96  
% 3.85/0.96  % (5485)Memory used [KB]: 14328
% 3.85/0.96  % (5485)Time elapsed: 0.520 s
% 3.85/0.96  % (5485)------------------------------
% 3.85/0.96  % (5485)------------------------------
% 3.85/0.96  % (5662)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 4.25/1.04  % (5486)Time limit reached!
% 4.25/1.04  % (5486)------------------------------
% 4.25/1.04  % (5486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.25/1.04  % (5486)Termination reason: Time limit
% 4.25/1.04  
% 4.25/1.04  % (5486)Memory used [KB]: 7547
% 4.25/1.04  % (5486)Time elapsed: 0.606 s
% 4.25/1.04  % (5486)------------------------------
% 4.25/1.04  % (5486)------------------------------
% 4.25/1.06  % (5690)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 4.25/1.07  % (5688)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 4.57/1.15  % (5715)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 4.57/1.15  % (5690)Refutation not found, incomplete strategy% (5690)------------------------------
% 4.57/1.15  % (5690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.57/1.16  % (5690)Termination reason: Refutation not found, incomplete strategy
% 4.57/1.16  
% 4.57/1.16  % (5690)Memory used [KB]: 6140
% 4.57/1.16  % (5690)Time elapsed: 0.141 s
% 4.57/1.16  % (5690)------------------------------
% 4.57/1.16  % (5690)------------------------------
% 6.51/1.20  % (5530)Refutation found. Thanks to Tanya!
% 6.51/1.20  % SZS status Theorem for theBenchmark
% 6.51/1.20  % SZS output start Proof for theBenchmark
% 6.51/1.20  fof(f3182,plain,(
% 6.51/1.20    $false),
% 6.51/1.20    inference(subsumption_resolution,[],[f3163,f117])).
% 6.51/1.20  fof(f117,plain,(
% 6.51/1.20    ~r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 6.51/1.20    inference(unit_resulting_resolution,[],[f38,f99])).
% 6.51/1.20  fof(f99,plain,(
% 6.51/1.20    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 6.51/1.20    inference(equality_resolution,[],[f87])).
% 6.51/1.20  fof(f87,plain,(
% 6.51/1.20    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 6.51/1.20    inference(definition_unfolding,[],[f46,f76])).
% 6.51/1.20  fof(f76,plain,(
% 6.51/1.20    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 6.51/1.20    inference(definition_unfolding,[],[f50,f75])).
% 6.51/1.20  fof(f75,plain,(
% 6.51/1.20    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 6.51/1.20    inference(definition_unfolding,[],[f69,f74])).
% 6.51/1.20  fof(f74,plain,(
% 6.51/1.20    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 6.51/1.20    inference(definition_unfolding,[],[f52,f73])).
% 6.51/1.20  fof(f73,plain,(
% 6.51/1.20    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 6.51/1.20    inference(definition_unfolding,[],[f51,f72])).
% 6.51/1.20  fof(f72,plain,(
% 6.51/1.20    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 6.51/1.20    inference(definition_unfolding,[],[f53,f71])).
% 6.51/1.20  fof(f71,plain,(
% 6.51/1.20    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 6.51/1.20    inference(definition_unfolding,[],[f55,f54])).
% 6.51/1.20  fof(f54,plain,(
% 6.51/1.20    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 6.51/1.20    inference(cnf_transformation,[],[f21])).
% 6.51/1.20  fof(f21,axiom,(
% 6.51/1.20    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 6.51/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 6.51/1.20  fof(f55,plain,(
% 6.51/1.20    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 6.51/1.20    inference(cnf_transformation,[],[f20])).
% 6.51/1.20  fof(f20,axiom,(
% 6.51/1.20    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 6.51/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 6.51/1.20  fof(f53,plain,(
% 6.51/1.20    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 6.51/1.20    inference(cnf_transformation,[],[f19])).
% 6.51/1.20  fof(f19,axiom,(
% 6.51/1.20    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 6.51/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 6.51/1.20  fof(f51,plain,(
% 6.51/1.20    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 6.51/1.20    inference(cnf_transformation,[],[f18])).
% 6.51/1.20  fof(f18,axiom,(
% 6.51/1.20    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 6.51/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 6.51/1.20  fof(f52,plain,(
% 6.51/1.20    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.51/1.20    inference(cnf_transformation,[],[f17])).
% 6.51/1.20  fof(f17,axiom,(
% 6.51/1.20    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.51/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 6.51/1.20  fof(f69,plain,(
% 6.51/1.20    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 6.51/1.20    inference(cnf_transformation,[],[f16])).
% 6.51/1.20  fof(f16,axiom,(
% 6.51/1.20    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 6.51/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 6.51/1.20  fof(f50,plain,(
% 6.51/1.20    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 6.51/1.20    inference(cnf_transformation,[],[f15])).
% 6.51/1.20  fof(f15,axiom,(
% 6.51/1.20    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 6.51/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 6.51/1.20  fof(f46,plain,(
% 6.51/1.20    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 6.51/1.20    inference(cnf_transformation,[],[f31])).
% 6.51/1.20  fof(f31,plain,(
% 6.51/1.20    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 6.51/1.20    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 6.51/1.20  fof(f30,plain,(
% 6.51/1.20    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 6.51/1.20    introduced(choice_axiom,[])).
% 6.51/1.20  fof(f29,plain,(
% 6.51/1.20    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 6.51/1.20    inference(rectify,[],[f28])).
% 6.51/1.20  fof(f28,plain,(
% 6.51/1.20    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 6.51/1.20    inference(nnf_transformation,[],[f9])).
% 6.51/1.20  fof(f9,axiom,(
% 6.51/1.20    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 6.51/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 6.51/1.20  fof(f38,plain,(
% 6.51/1.20    sK0 != sK1),
% 6.51/1.20    inference(cnf_transformation,[],[f27])).
% 6.51/1.20  fof(f27,plain,(
% 6.51/1.20    sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 6.51/1.20    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26])).
% 6.51/1.20  fof(f26,plain,(
% 6.51/1.20    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 6.51/1.20    introduced(choice_axiom,[])).
% 6.51/1.20  fof(f24,plain,(
% 6.51/1.20    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 6.51/1.20    inference(ennf_transformation,[],[f23])).
% 6.51/1.20  fof(f23,negated_conjecture,(
% 6.51/1.20    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 6.51/1.20    inference(negated_conjecture,[],[f22])).
% 6.51/1.20  fof(f22,conjecture,(
% 6.51/1.20    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 6.51/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 6.51/1.20  fof(f3163,plain,(
% 6.51/1.20    r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 6.51/1.20    inference(superposition,[],[f101,f3134])).
% 6.51/1.20  fof(f3134,plain,(
% 6.51/1.20    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 6.51/1.20    inference(forward_demodulation,[],[f3133,f2979])).
% 6.51/1.20  fof(f2979,plain,(
% 6.51/1.20    ( ! [X2,X0,X1] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,X0,X1,X2),k1_xboole_0) = k6_enumset1(sK0,X0,X1,X2,sK0,sK0,sK0,sK0)) )),
% 6.51/1.20    inference(backward_demodulation,[],[f2618,f2978])).
% 6.51/1.20  fof(f2978,plain,(
% 6.51/1.20    ( ! [X12,X13,X11] : (k6_enumset1(sK0,X11,X12,X13,sK1,sK0,sK0,sK0) = k6_enumset1(sK0,X11,X12,X13,sK0,sK0,sK0,sK0)) )),
% 6.51/1.20    inference(backward_demodulation,[],[f2626,f2977])).
% 6.51/1.20  fof(f2977,plain,(
% 6.51/1.20    ( ! [X2,X0,X1] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X0,X1,X2,sK1),k1_xboole_0) = k6_enumset1(sK0,X0,X1,X2,sK0,sK0,sK0,sK0)) )),
% 6.51/1.20    inference(forward_demodulation,[],[f2961,f1380])).
% 6.51/1.20  fof(f1380,plain,(
% 6.51/1.20    ( ! [X4,X2,X5,X3] : (k1_xboole_0 = k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5),k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5))) )),
% 6.51/1.20    inference(backward_demodulation,[],[f1378,f1379])).
% 6.51/1.20  fof(f1379,plain,(
% 6.51/1.20    ( ! [X6,X8,X7,X9] : (k6_enumset1(X6,X6,X6,X6,X6,X7,X8,X9) = k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X7,X8,X9),k6_enumset1(X6,X7,X8,X9,sK0,sK0,sK0,sK0))) )),
% 6.51/1.20    inference(forward_demodulation,[],[f1216,f1277])).
% 6.51/1.20  fof(f1277,plain,(
% 6.51/1.20    ( ! [X6,X4,X7,X5] : (k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X5,X6,X7,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X4,X4,X4,X4,X5,X6,X7,sK1)))) = k6_enumset1(X4,X5,X6,X7,sK0,sK0,sK0,sK0)) )),
% 6.51/1.20    inference(forward_demodulation,[],[f1231,f78])).
% 6.51/1.20  fof(f78,plain,(
% 6.51/1.20    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3))))) )),
% 6.51/1.20    inference(definition_unfolding,[],[f42,f70,f73,f73])).
% 6.51/1.20  fof(f70,plain,(
% 6.51/1.20    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 6.51/1.20    inference(definition_unfolding,[],[f44,f57])).
% 6.51/1.20  fof(f57,plain,(
% 6.51/1.20    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.51/1.20    inference(cnf_transformation,[],[f2])).
% 6.51/1.20  fof(f2,axiom,(
% 6.51/1.20    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.51/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 6.51/1.20  fof(f44,plain,(
% 6.51/1.20    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 6.51/1.20    inference(cnf_transformation,[],[f7])).
% 6.51/1.20  fof(f7,axiom,(
% 6.51/1.20    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 6.51/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 6.51/1.20  fof(f42,plain,(
% 6.51/1.20    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 6.51/1.20    inference(cnf_transformation,[],[f11])).
% 6.51/1.20  fof(f11,axiom,(
% 6.51/1.20    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 6.51/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).
% 6.51/1.20  fof(f1231,plain,(
% 6.51/1.20    ( ! [X6,X4,X7,X5] : (k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X5,X6,X7,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X4,X4,X4,X4,X5,X6,X7,sK1)))) = k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7))))) )),
% 6.51/1.20    inference(backward_demodulation,[],[f208,f1225])).
% 6.51/1.20  fof(f1225,plain,(
% 6.51/1.20    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 6.51/1.20    inference(forward_demodulation,[],[f1224,f58])).
% 6.51/1.20  fof(f58,plain,(
% 6.51/1.20    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.51/1.20    inference(cnf_transformation,[],[f5])).
% 6.51/1.20  fof(f5,axiom,(
% 6.51/1.20    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 6.51/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 6.51/1.20  fof(f1224,plain,(
% 6.51/1.20    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 6.51/1.20    inference(forward_demodulation,[],[f1223,f197])).
% 6.51/1.20  fof(f197,plain,(
% 6.51/1.20    k6_enumset1(sK1,sK1,sK1,sK1,sK0,sK0,sK0,sK0) = k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 6.51/1.20    inference(backward_demodulation,[],[f195,f196])).
% 6.51/1.20  fof(f196,plain,(
% 6.51/1.20    k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK1,sK1,sK1,sK0,sK0,sK0,sK0,sK0)),
% 6.51/1.20    inference(backward_demodulation,[],[f194,f189])).
% 6.51/1.20  fof(f189,plain,(
% 6.51/1.20    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 6.51/1.20    inference(superposition,[],[f82,f171])).
% 6.51/1.20  fof(f171,plain,(
% 6.51/1.20    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 6.51/1.20    inference(forward_demodulation,[],[f170,f83])).
% 6.51/1.20  fof(f83,plain,(
% 6.51/1.20    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 6.51/1.20    inference(definition_unfolding,[],[f45,f70])).
% 6.51/1.20  fof(f45,plain,(
% 6.51/1.20    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 6.51/1.20    inference(cnf_transformation,[],[f3])).
% 6.51/1.20  fof(f3,axiom,(
% 6.51/1.20    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 6.51/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 6.51/1.20  fof(f170,plain,(
% 6.51/1.20    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) )),
% 6.51/1.20    inference(forward_demodulation,[],[f167,f58])).
% 6.51/1.20  fof(f167,plain,(
% 6.51/1.20    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0))) )),
% 6.51/1.20    inference(superposition,[],[f141,f88])).
% 6.51/1.20  fof(f88,plain,(
% 6.51/1.20    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 6.51/1.20    inference(definition_unfolding,[],[f59,f57,f70])).
% 6.51/1.20  fof(f59,plain,(
% 6.51/1.20    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 6.51/1.20    inference(cnf_transformation,[],[f4])).
% 6.51/1.20  fof(f4,axiom,(
% 6.51/1.20    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 6.51/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 6.51/1.20  fof(f141,plain,(
% 6.51/1.20    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)))) )),
% 6.51/1.20    inference(forward_demodulation,[],[f140,f56])).
% 6.51/1.20  fof(f56,plain,(
% 6.51/1.20    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 6.51/1.20    inference(cnf_transformation,[],[f6])).
% 6.51/1.20  fof(f6,axiom,(
% 6.51/1.20    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 6.51/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 6.51/1.20  fof(f140,plain,(
% 6.51/1.20    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) )),
% 6.51/1.20    inference(superposition,[],[f56,f107])).
% 6.51/1.20  fof(f107,plain,(
% 6.51/1.20    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 6.51/1.20    inference(forward_demodulation,[],[f79,f60])).
% 6.51/1.20  fof(f60,plain,(
% 6.51/1.20    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.51/1.20    inference(cnf_transformation,[],[f1])).
% 6.51/1.20  fof(f1,axiom,(
% 6.51/1.20    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.51/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 6.51/1.20  fof(f79,plain,(
% 6.51/1.20    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 6.51/1.20    inference(definition_unfolding,[],[f37,f76,f70,f76,f76])).
% 6.51/1.20  fof(f37,plain,(
% 6.51/1.20    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 6.51/1.20    inference(cnf_transformation,[],[f27])).
% 6.51/1.20  fof(f82,plain,(
% 6.51/1.20    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) )),
% 6.51/1.20    inference(definition_unfolding,[],[f43,f70,f76,f54])).
% 6.51/1.20  fof(f43,plain,(
% 6.51/1.20    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) )),
% 6.51/1.20    inference(cnf_transformation,[],[f14])).
% 6.51/1.20  fof(f14,axiom,(
% 6.51/1.20    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 6.51/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).
% 6.51/1.20  fof(f194,plain,(
% 6.51/1.20    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k6_enumset1(sK1,sK1,sK1,sK0,sK0,sK0,sK0,sK0)),
% 6.51/1.20    inference(forward_demodulation,[],[f188,f78])).
% 6.51/1.20  fof(f188,plain,(
% 6.51/1.20    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0))))),
% 6.51/1.20    inference(superposition,[],[f80,f171])).
% 6.51/1.20  fof(f80,plain,(
% 6.51/1.20    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3))))) )),
% 6.51/1.20    inference(definition_unfolding,[],[f40,f77,f70,f73,f72])).
% 6.51/1.20  fof(f77,plain,(
% 6.51/1.20    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))))) )),
% 6.51/1.20    inference(definition_unfolding,[],[f39,f70,f72,f73])).
% 6.51/1.20  fof(f39,plain,(
% 6.51/1.20    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 6.51/1.20    inference(cnf_transformation,[],[f13])).
% 6.51/1.20  fof(f13,axiom,(
% 6.51/1.20    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 6.51/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).
% 6.51/1.20  fof(f40,plain,(
% 6.51/1.20    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))) )),
% 6.51/1.20    inference(cnf_transformation,[],[f10])).
% 6.51/1.20  fof(f10,axiom,(
% 6.51/1.20    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))),
% 6.51/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l142_enumset1)).
% 6.51/1.20  fof(f195,plain,(
% 6.51/1.20    k6_enumset1(sK1,sK1,sK1,sK1,sK0,sK0,sK0,sK0) = k6_enumset1(sK1,sK1,sK1,sK0,sK0,sK0,sK0,sK0)),
% 6.51/1.20    inference(backward_demodulation,[],[f187,f194])).
% 6.51/1.20  fof(f187,plain,(
% 6.51/1.20    k6_enumset1(sK1,sK1,sK1,sK1,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 6.51/1.20    inference(superposition,[],[f78,f171])).
% 6.51/1.20  fof(f1223,plain,(
% 6.51/1.20    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK0,sK0,sK0,sK0)),
% 6.51/1.20    inference(forward_demodulation,[],[f1222,f78])).
% 6.51/1.20  fof(f1222,plain,(
% 6.51/1.20    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 6.51/1.20    inference(forward_demodulation,[],[f1221,f616])).
% 6.51/1.20  fof(f616,plain,(
% 6.51/1.20    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 6.51/1.20    inference(backward_demodulation,[],[f603,f604])).
% 6.51/1.20  fof(f604,plain,(
% 6.51/1.20    ( ! [X2] : (k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,sK1,sK1,sK0,sK0,sK0,sK0,sK0))) )),
% 6.51/1.20    inference(superposition,[],[f83,f204])).
% 6.51/1.20  fof(f204,plain,(
% 6.51/1.20    ( ! [X0] : (k6_enumset1(X0,sK1,sK1,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) )),
% 6.51/1.20    inference(superposition,[],[f82,f196])).
% 6.51/1.20  fof(f603,plain,(
% 6.51/1.20    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,sK1,sK1,sK0,sK0,sK0,sK0,sK0)))) )),
% 6.51/1.20    inference(superposition,[],[f88,f204])).
% 6.51/1.20  fof(f1221,plain,(
% 6.51/1.20    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 6.51/1.20    inference(forward_demodulation,[],[f1198,f897])).
% 6.51/1.20  fof(f897,plain,(
% 6.51/1.20    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) )),
% 6.51/1.20    inference(backward_demodulation,[],[f542,f894])).
% 6.51/1.20  fof(f894,plain,(
% 6.51/1.20    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) )),
% 6.51/1.20    inference(superposition,[],[f56,f847])).
% 6.51/1.20  fof(f847,plain,(
% 6.51/1.20    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 6.51/1.20    inference(forward_demodulation,[],[f826,f58])).
% 6.51/1.20  fof(f826,plain,(
% 6.51/1.20    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 6.51/1.20    inference(superposition,[],[f413,f384])).
% 6.51/1.20  fof(f384,plain,(
% 6.51/1.20    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 6.51/1.20    inference(backward_demodulation,[],[f382,f383])).
% 6.51/1.20  fof(f383,plain,(
% 6.51/1.20    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))))),
% 6.51/1.20    inference(forward_demodulation,[],[f377,f60])).
% 6.51/1.20  fof(f377,plain,(
% 6.51/1.20    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))),
% 6.51/1.20    inference(superposition,[],[f83,f203])).
% 6.51/1.20  fof(f203,plain,(
% 6.51/1.20    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))) )),
% 6.51/1.20    inference(forward_demodulation,[],[f193,f56])).
% 6.51/1.20  fof(f193,plain,(
% 6.51/1.20    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) )),
% 6.51/1.20    inference(superposition,[],[f56,f171])).
% 6.51/1.20  fof(f382,plain,(
% 6.51/1.20    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))))),
% 6.51/1.20    inference(forward_demodulation,[],[f376,f60])).
% 6.51/1.20  fof(f376,plain,(
% 6.51/1.20    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))),
% 6.51/1.20    inference(superposition,[],[f88,f203])).
% 6.51/1.20  fof(f413,plain,(
% 6.51/1.20    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) )),
% 6.51/1.20    inference(superposition,[],[f56,f384])).
% 6.51/1.20  fof(f542,plain,(
% 6.51/1.20    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) )),
% 6.51/1.20    inference(superposition,[],[f253,f305])).
% 6.51/1.20  fof(f305,plain,(
% 6.51/1.20    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)))) )),
% 6.51/1.20    inference(forward_demodulation,[],[f304,f56])).
% 6.51/1.20  fof(f304,plain,(
% 6.51/1.20    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0))) )),
% 6.51/1.20    inference(superposition,[],[f56,f189])).
% 6.51/1.20  fof(f253,plain,(
% 6.51/1.20    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 6.51/1.20    inference(superposition,[],[f56,f241])).
% 6.51/1.20  fof(f241,plain,(
% 6.51/1.20    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 6.51/1.20    inference(backward_demodulation,[],[f201,f235])).
% 6.51/1.20  fof(f235,plain,(
% 6.51/1.20    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 6.51/1.20    inference(superposition,[],[f202,f60])).
% 6.51/1.20  fof(f202,plain,(
% 6.51/1.20    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 6.51/1.20    inference(forward_demodulation,[],[f192,f189])).
% 6.51/1.20  fof(f192,plain,(
% 6.51/1.20    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 6.51/1.20    inference(superposition,[],[f83,f171])).
% 6.51/1.20  fof(f201,plain,(
% 6.51/1.20    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 6.51/1.20    inference(forward_demodulation,[],[f200,f60])).
% 6.51/1.20  fof(f200,plain,(
% 6.51/1.20    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 6.51/1.20    inference(forward_demodulation,[],[f191,f189])).
% 6.51/1.20  fof(f191,plain,(
% 6.51/1.20    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))),
% 6.51/1.20    inference(superposition,[],[f88,f171])).
% 6.51/1.20  fof(f1198,plain,(
% 6.51/1.20    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 6.51/1.20    inference(superposition,[],[f208,f235])).
% 6.51/1.20  fof(f208,plain,(
% 6.51/1.20    ( ! [X6,X4,X7,X5] : (k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X5,X6,X7,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X4,X4,X4,X4,X5,X6,X7,sK1)))) = k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7))))) )),
% 6.51/1.20    inference(superposition,[],[f80,f197])).
% 6.51/1.20  fof(f1216,plain,(
% 6.51/1.20    ( ! [X6,X8,X7,X9] : (k6_enumset1(X6,X6,X6,X6,X6,X7,X8,X9) = k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X7,X8,X9),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X7,X8,X9,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X6,X6,X6,X6,X7,X8,X9,sK1)))))) )),
% 6.51/1.20    inference(superposition,[],[f83,f208])).
% 6.51/1.20  fof(f1378,plain,(
% 6.51/1.20    ( ! [X4,X2,X5,X3] : (k1_xboole_0 = k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5),k6_enumset1(X2,X3,X4,X5,sK0,sK0,sK0,sK0)))) )),
% 6.51/1.20    inference(forward_demodulation,[],[f1215,f1277])).
% 6.51/1.20  fof(f1215,plain,(
% 6.51/1.20    ( ! [X4,X2,X5,X3] : (k1_xboole_0 = k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X3,X4,X5,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X2,X2,X2,X2,X3,X4,X5,sK1))))))) )),
% 6.51/1.20    inference(superposition,[],[f88,f208])).
% 6.51/1.20  fof(f2961,plain,(
% 6.51/1.20    ( ! [X2,X0,X1] : (k6_enumset1(sK0,X0,X1,X2,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X0,X1,X2,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) )),
% 6.51/1.20    inference(superposition,[],[f1277,f1334])).
% 6.51/1.20  fof(f1334,plain,(
% 6.51/1.20    ( ! [X10,X8,X11,X9] : (k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,X8,X9,X10,X11))) )),
% 6.51/1.20    inference(forward_demodulation,[],[f1254,f1278])).
% 6.51/1.20  fof(f1278,plain,(
% 6.51/1.20    ( ! [X2,X0,X3,X1] : (k6_enumset1(sK0,sK0,sK0,sK0,X0,X1,X2,X3) = k6_enumset1(sK1,sK0,sK0,sK0,X0,X1,X2,X3)) )),
% 6.51/1.20    inference(forward_demodulation,[],[f1232,f78])).
% 6.51/1.20  fof(f1232,plain,(
% 6.51/1.20    ( ! [X2,X0,X3,X1] : (k6_enumset1(sK1,sK0,sK0,sK0,X0,X1,X2,X3) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) )),
% 6.51/1.20    inference(backward_demodulation,[],[f212,f1225])).
% 6.51/1.20  fof(f212,plain,(
% 6.51/1.20    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k6_enumset1(sK1,sK0,sK0,sK0,X0,X1,X2,X3)) )),
% 6.51/1.20    inference(forward_demodulation,[],[f207,f82])).
% 6.51/1.20  fof(f207,plain,(
% 6.51/1.20    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X0,X1,X2,X3),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X0,X1,X2,X3),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) )),
% 6.51/1.20    inference(superposition,[],[f81,f197])).
% 6.51/1.20  fof(f81,plain,(
% 6.51/1.20    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) )),
% 6.51/1.20    inference(definition_unfolding,[],[f41,f77,f70,f76])).
% 6.51/1.20  fof(f41,plain,(
% 6.51/1.20    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))) )),
% 6.51/1.20    inference(cnf_transformation,[],[f12])).
% 6.51/1.20  fof(f12,axiom,(
% 6.51/1.20    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))),
% 6.51/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).
% 6.51/1.20  fof(f1254,plain,(
% 6.51/1.20    ( ! [X10,X8,X11,X9] : (k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK0,sK0,sK0,X8,X9,X10,X11))) )),
% 6.51/1.20    inference(backward_demodulation,[],[f770,f1225])).
% 6.51/1.20  fof(f770,plain,(
% 6.51/1.20    ( ! [X10,X8,X11,X9] : (k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK0,sK0,sK0,X8,X9,X10,X11))) )),
% 6.51/1.20    inference(superposition,[],[f83,f212])).
% 6.51/1.20  fof(f2626,plain,(
% 6.51/1.20    ( ! [X12,X13,X11] : (k6_enumset1(sK0,X11,X12,X13,sK1,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X11,X12,X13,sK1),k1_xboole_0)) )),
% 6.51/1.20    inference(forward_demodulation,[],[f2625,f1380])).
% 6.51/1.20  fof(f2625,plain,(
% 6.51/1.20    ( ! [X12,X13,X11] : (k6_enumset1(sK0,X11,X12,X13,sK1,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X11,X12,X13,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0)))) )),
% 6.51/1.20    inference(forward_demodulation,[],[f2624,f1281])).
% 6.51/1.20  fof(f1281,plain,(
% 6.51/1.20    ( ! [X19,X17,X20,X18] : (k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,X17,X18,X19,X20))) )),
% 6.51/1.20    inference(backward_demodulation,[],[f802,f1278])).
% 6.51/1.20  fof(f802,plain,(
% 6.51/1.20    ( ! [X19,X17,X20,X18] : (k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k6_enumset1(sK1,sK0,sK0,sK0,X17,X18,X19,X20))) )),
% 6.51/1.20    inference(superposition,[],[f83,f213])).
% 6.51/1.20  fof(f213,plain,(
% 6.51/1.20    ( ! [X10,X8,X11,X9] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X8,X9,X10,X11),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X8,X9,X10,X11),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0)))) = k6_enumset1(sK1,sK0,sK0,sK0,X8,X9,X10,X11)) )),
% 6.51/1.20    inference(forward_demodulation,[],[f209,f212])).
% 6.51/1.20  fof(f209,plain,(
% 6.51/1.20    ( ! [X10,X8,X11,X9] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X8,X9,X10,X11),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X8,X9,X10,X11),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0)))) = k5_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X9,X10,X11),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X9,X10,X11),k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) )),
% 6.51/1.20    inference(superposition,[],[f80,f197])).
% 6.51/1.20  fof(f2624,plain,(
% 6.51/1.20    ( ! [X12,X13,X11] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X11,X12,X13,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,X11,X12,X13,sK1)))) = k6_enumset1(sK0,X11,X12,X13,sK1,sK0,sK0,sK0)) )),
% 6.51/1.20    inference(forward_demodulation,[],[f2623,f2618])).
% 6.51/1.20  fof(f2623,plain,(
% 6.51/1.20    ( ! [X12,X13,X11] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X11,X12,X13,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,X11,X12,X13,sK1)))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,X11,X12,X13),k1_xboole_0)) )),
% 6.51/1.20    inference(forward_demodulation,[],[f2610,f1380])).
% 6.51/1.20  fof(f2610,plain,(
% 6.51/1.20    ( ! [X12,X13,X11] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,X11,X12,X13,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,X11,X12,X13,sK1)))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,X11,X12,X13),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0)))) )),
% 6.51/1.20    inference(superposition,[],[f80,f1281])).
% 6.51/1.20  fof(f2618,plain,(
% 6.51/1.20    ( ! [X2,X0,X1] : (k6_enumset1(sK0,X0,X1,X2,sK1,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,X0,X1,X2),k1_xboole_0)) )),
% 6.51/1.20    inference(forward_demodulation,[],[f2607,f1380])).
% 6.51/1.20  fof(f2607,plain,(
% 6.51/1.20    ( ! [X2,X0,X1] : (k6_enumset1(sK0,X0,X1,X2,sK1,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,X0,X1,X2),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK0,sK0)))) )),
% 6.51/1.20    inference(superposition,[],[f78,f1281])).
% 6.51/1.20  fof(f3133,plain,(
% 6.51/1.20    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),
% 6.51/1.20    inference(forward_demodulation,[],[f3104,f1380])).
% 6.51/1.20  fof(f3104,plain,(
% 6.51/1.20    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 6.51/1.20    inference(superposition,[],[f78,f1359])).
% 6.51/1.20  fof(f1359,plain,(
% 6.51/1.20    ( ! [X21,X19,X22,X20] : (k6_enumset1(X19,X19,X19,X19,X20,X21,X22,sK1) = k3_xboole_0(k6_enumset1(X19,X19,X19,X19,X20,X21,X22,sK1),k6_enumset1(X19,X20,X21,X22,sK0,sK0,sK0,sK0))) )),
% 6.51/1.20    inference(forward_demodulation,[],[f1358,f78])).
% 6.51/1.20  fof(f1358,plain,(
% 6.51/1.20    ( ! [X21,X19,X22,X20] : (k6_enumset1(X19,X19,X19,X19,X20,X21,X22,sK1) = k3_xboole_0(k6_enumset1(X19,X19,X19,X19,X20,X21,X22,sK1),k5_xboole_0(k6_enumset1(X19,X19,X19,X19,X19,X20,X21,X22),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X19,X19,X19,X19,X19,X20,X21,X22)))))) )),
% 6.51/1.20    inference(forward_demodulation,[],[f1208,f1225])).
% 6.51/1.20  fof(f1208,plain,(
% 6.51/1.20    ( ! [X21,X19,X22,X20] : (k6_enumset1(X19,X19,X19,X19,X20,X21,X22,sK1) = k3_xboole_0(k6_enumset1(X19,X19,X19,X19,X20,X21,X22,sK1),k5_xboole_0(k6_enumset1(X19,X19,X19,X19,X19,X20,X21,X22),k5_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X19,X19,X19,X19,X19,X20,X21,X22)))))) )),
% 6.51/1.20    inference(superposition,[],[f83,f208])).
% 6.51/1.20  fof(f101,plain,(
% 6.51/1.20    ( ! [X0,X5,X1] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5))) )),
% 6.51/1.20    inference(equality_resolution,[],[f100])).
% 6.51/1.20  fof(f100,plain,(
% 6.51/1.20    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 6.51/1.20    inference(equality_resolution,[],[f93])).
% 6.51/1.20  fof(f93,plain,(
% 6.51/1.20    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 6.51/1.20    inference(definition_unfolding,[],[f64,f74])).
% 6.51/1.20  fof(f64,plain,(
% 6.51/1.20    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 6.51/1.20    inference(cnf_transformation,[],[f36])).
% 6.51/1.20  fof(f36,plain,(
% 6.51/1.20    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 6.51/1.20    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).
% 6.51/1.20  fof(f35,plain,(
% 6.51/1.20    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 6.51/1.20    introduced(choice_axiom,[])).
% 6.51/1.20  fof(f34,plain,(
% 6.51/1.20    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 6.51/1.20    inference(rectify,[],[f33])).
% 6.51/1.20  fof(f33,plain,(
% 6.51/1.20    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 6.51/1.20    inference(flattening,[],[f32])).
% 6.51/1.20  fof(f32,plain,(
% 6.51/1.20    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 6.51/1.20    inference(nnf_transformation,[],[f25])).
% 6.51/1.20  fof(f25,plain,(
% 6.51/1.20    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 6.51/1.20    inference(ennf_transformation,[],[f8])).
% 6.51/1.20  fof(f8,axiom,(
% 6.51/1.20    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 6.51/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 6.51/1.20  % SZS output end Proof for theBenchmark
% 6.51/1.20  % (5530)------------------------------
% 6.51/1.20  % (5530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.51/1.20  % (5530)Termination reason: Refutation
% 6.51/1.20  
% 6.51/1.20  % (5530)Memory used [KB]: 13816
% 6.51/1.20  % (5530)Time elapsed: 0.512 s
% 6.51/1.20  % (5530)------------------------------
% 6.51/1.20  % (5530)------------------------------
% 6.51/1.20  % (5478)Success in time 0.835 s
%------------------------------------------------------------------------------
