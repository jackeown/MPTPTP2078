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
% DateTime   : Thu Dec  3 12:41:26 EST 2020

% Result     : Theorem 32.77s
% Output     : Refutation 32.77s
% Verified   : 
% Statistics : Number of formulae       :  135 (3947 expanded)
%              Number of leaves         :   17 (1169 expanded)
%              Depth                    :   41
%              Number of atoms          :  463 (11705 expanded)
%              Number of equality atoms :  210 (5687 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22535,plain,(
    $false ),
    inference(subsumption_resolution,[],[f22438,f81])).

fof(f81,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f52,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
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
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f22438,plain,(
    ~ r2_hidden(sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f9572,f22290])).

fof(f22290,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(subsumption_resolution,[],[f22164,f9573])).

fof(f9573,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f9561,f5665])).

fof(f5665,plain,(
    r2_hidden(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f5622])).

fof(f5622,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f5444,f79])).

fof(f79,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f53,f62])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5444,plain,(
    ! [X32] :
      ( ~ r2_hidden(X32,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
      | r2_hidden(X32,sK2)
      | r2_hidden(sK1,sK2) ) ),
    inference(superposition,[],[f77,f4957])).

fof(f4957,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | r2_hidden(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f4895])).

fof(f4895,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(superposition,[],[f201,f4836])).

fof(f4836,plain,(
    ! [X6] :
      ( k5_xboole_0(k1_xboole_0,X6) = X6
      | r2_hidden(sK1,sK2) ) ),
    inference(forward_demodulation,[],[f4791,f36])).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f4791,plain,(
    ! [X6] :
      ( k5_xboole_0(X6,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X6,k1_xboole_0))
      | r2_hidden(sK1,sK2) ) ),
    inference(superposition,[],[f4725,f38])).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f4725,plain,(
    ! [X18] :
      ( k5_xboole_0(k1_xboole_0,X18) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X18))
      | r2_hidden(sK1,sK2) ) ),
    inference(duplicate_literal_removal,[],[f4689])).

fof(f4689,plain,(
    ! [X18] :
      ( k5_xboole_0(k1_xboole_0,X18) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X18))
      | r2_hidden(sK1,sK2)
      | r2_hidden(sK1,sK2) ) ),
    inference(superposition,[],[f3365,f3226])).

fof(f3226,plain,(
    ! [X0] :
      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X0))
      | r2_hidden(sK1,sK2) ) ),
    inference(superposition,[],[f2852,f38])).

fof(f2852,plain,(
    ! [X9] :
      ( k5_xboole_0(k1_xboole_0,X9) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X9,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
      | r2_hidden(sK1,sK2) ) ),
    inference(forward_demodulation,[],[f2843,f36])).

fof(f2843,plain,(
    ! [X9] :
      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X9,k1_xboole_0)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X9,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
      | r2_hidden(sK1,sK2) ) ),
    inference(duplicate_literal_removal,[],[f2787])).

fof(f2787,plain,(
    ! [X9] :
      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X9,k1_xboole_0)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X9,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
      | r2_hidden(sK1,sK2)
      | r2_hidden(sK1,sK2) ) ),
    inference(superposition,[],[f504,f201])).

fof(f504,plain,(
    ! [X2,X3] :
      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))
      | r2_hidden(sK1,sK2) ) ),
    inference(superposition,[],[f194,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f194,plain,(
    ! [X0] :
      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X0,k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
      | r2_hidden(sK1,sK2) ) ),
    inference(superposition,[],[f95,f38])).

fof(f95,plain,(
    ! [X0] :
      ( k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0)) = k5_xboole_0(k1_xboole_0,X0)
      | r2_hidden(sK1,sK2) ) ),
    inference(superposition,[],[f42,f86])).

fof(f86,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f65,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f65,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f33,f40,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f62])).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f33,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( r2_hidden(sK1,sK2)
        & r2_hidden(sK0,sK2) )
      | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK0,sK2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( r2_hidden(sK1,sK2)
          & r2_hidden(sK0,sK2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f3365,plain,(
    ! [X0] :
      ( k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X0))
      | r2_hidden(sK1,sK2) ) ),
    inference(superposition,[],[f2854,f38])).

fof(f2854,plain,(
    ! [X11] :
      ( k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X11) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X11,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
      | r2_hidden(sK1,sK2) ) ),
    inference(forward_demodulation,[],[f2842,f36])).

fof(f2842,plain,(
    ! [X11] :
      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X11,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X11,k1_xboole_0))
      | r2_hidden(sK1,sK2) ) ),
    inference(duplicate_literal_removal,[],[f2789])).

fof(f2789,plain,(
    ! [X11] :
      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X11,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X11,k1_xboole_0))
      | r2_hidden(sK1,sK2)
      | r2_hidden(sK1,sK2) ) ),
    inference(superposition,[],[f504,f86])).

fof(f201,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f192,f36])).

fof(f192,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k1_xboole_0)
    | r2_hidden(sK1,sK2) ),
    inference(superposition,[],[f95,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f77,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f9561,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f9493])).

fof(f9493,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(superposition,[],[f1945,f7717])).

fof(f7717,plain,
    ( sK0 = sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f7708,f5665])).

fof(f7708,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | sK0 = sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f7652])).

fof(f7652,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | sK0 = sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f1945,f7622])).

fof(f7622,plain,
    ( sK1 = sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK0,sK2)
    | sK0 = sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(subsumption_resolution,[],[f768,f5665])).

fof(f768,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2)
    | sK1 = sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | sK0 = sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f760])).

fof(f760,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2)
    | sK1 = sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | sK0 = sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | sK0 = sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(resolution,[],[f375,f84])).

fof(f84,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f50,f62])).

fof(f50,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f375,plain,
    ( r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(trivial_inequality_removal,[],[f374])).

fof(f374,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f370])).

fof(f370,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f127,f35])).

fof(f127,plain,(
    ! [X1] :
      ( k1_xboole_0 != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X1)
      | ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
      | r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X1),X1) ) ),
    inference(superposition,[],[f85,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f85,plain,
    ( k1_xboole_0 != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f64,f37])).

fof(f64,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | k1_xboole_0 != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f34,f40,f63])).

fof(f34,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f1945,plain,
    ( ~ r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f439,f375])).

fof(f439,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2) ),
    inference(trivial_inequality_removal,[],[f438])).

fof(f438,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2) ),
    inference(duplicate_literal_removal,[],[f434])).

fof(f434,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2)
    | ~ r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f128,f35])).

fof(f128,plain,(
    ! [X2] :
      ( k1_xboole_0 != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X2)
      | ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | ~ r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
      | ~ r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X2),sK2)
      | ~ r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X2),X2) ) ),
    inference(superposition,[],[f85,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f22164,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | r2_hidden(sK0,sK2) ),
    inference(backward_demodulation,[],[f231,f22035])).

fof(f22035,plain,(
    ! [X22] : k5_xboole_0(k1_xboole_0,X22) = X22 ),
    inference(forward_demodulation,[],[f21955,f36])).

fof(f21955,plain,(
    ! [X22] : k5_xboole_0(X22,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X22,k1_xboole_0)) ),
    inference(superposition,[],[f21625,f38])).

fof(f21625,plain,(
    ! [X39] : k5_xboole_0(k1_xboole_0,X39) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X39)) ),
    inference(superposition,[],[f21441,f36])).

fof(f21441,plain,(
    ! [X4,X5] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X4,X5)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X5,X4)) ),
    inference(subsumption_resolution,[],[f21271,f9573])).

fof(f21271,plain,(
    ! [X4,X5] :
      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X4,X5)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X5,X4))
      | r2_hidden(sK0,sK2) ) ),
    inference(backward_demodulation,[],[f553,f21270])).

fof(f21270,plain,(
    ! [X4,X3] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X3))) ),
    inference(subsumption_resolution,[],[f3061,f9573])).

fof(f3061,plain,(
    ! [X4,X3] :
      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X3)))
      | r2_hidden(sK0,sK2) ) ),
    inference(forward_demodulation,[],[f2996,f42])).

fof(f2996,plain,(
    ! [X4,X3] :
      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(X4,k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),X3))
      | r2_hidden(sK0,sK2) ) ),
    inference(superposition,[],[f534,f38])).

fof(f534,plain,(
    ! [X2,X3] :
      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))
      | r2_hidden(sK0,sK2) ) ),
    inference(superposition,[],[f224,f42])).

fof(f224,plain,(
    ! [X0] :
      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X0,k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
      | r2_hidden(sK0,sK2) ) ),
    inference(superposition,[],[f117,f38])).

fof(f117,plain,(
    ! [X0] :
      ( k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0)) = k5_xboole_0(k1_xboole_0,X0)
      | r2_hidden(sK0,sK2) ) ),
    inference(superposition,[],[f42,f87])).

fof(f87,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f66,f37])).

fof(f66,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f32,f40,f63])).

fof(f32,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f553,plain,(
    ! [X4,X5] :
      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X4,X5)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X5)))
      | r2_hidden(sK0,sK2) ) ),
    inference(forward_demodulation,[],[f552,f42])).

fof(f552,plain,(
    ! [X4,X5] :
      ( k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(X4,k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),X5)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X4,X5))
      | r2_hidden(sK0,sK2) ) ),
    inference(forward_demodulation,[],[f542,f42])).

fof(f542,plain,(
    ! [X4,X5] :
      ( k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(X4,k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),X5)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X4),X5)
      | r2_hidden(sK0,sK2) ) ),
    inference(superposition,[],[f42,f224])).

fof(f231,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f222,f36])).

fof(f222,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k1_xboole_0)
    | r2_hidden(sK0,sK2) ),
    inference(superposition,[],[f117,f35])).

fof(f9572,plain,(
    ! [X1] : ~ r2_hidden(sK0,k3_xboole_0(sK2,X1)) ),
    inference(subsumption_resolution,[],[f9571,f77])).

fof(f9571,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK0,k3_xboole_0(sK2,X1))
      | ~ r2_hidden(sK0,sK2) ) ),
    inference(subsumption_resolution,[],[f9562,f5665])).

fof(f9562,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK0,k3_xboole_0(sK2,X1))
      | ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f9492])).

fof(f9492,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK0,k3_xboole_0(sK2,X1))
      | ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | ~ r2_hidden(sK0,sK2) ) ),
    inference(superposition,[],[f1959,f7717])).

fof(f1959,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_xboole_0(sK2,X0))
      | ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2) ) ),
    inference(resolution,[],[f1945,f77])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (12045)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (12062)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (12052)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (12054)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (12047)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (12043)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (12048)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (12060)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (12036)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (12037)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (12058)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (12056)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (12049)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (12039)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (12035)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (12043)Refutation not found, incomplete strategy% (12043)------------------------------
% 0.21/0.54  % (12043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12046)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (12040)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (12041)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (12044)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (12043)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12043)Memory used [KB]: 10874
% 0.21/0.54  % (12043)Time elapsed: 0.130 s
% 0.21/0.54  % (12043)------------------------------
% 0.21/0.54  % (12043)------------------------------
% 0.21/0.54  % (12042)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (12038)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (12059)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (12064)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (12053)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (12065)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (12053)Refutation not found, incomplete strategy% (12053)------------------------------
% 0.21/0.55  % (12053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (12053)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (12053)Memory used [KB]: 10746
% 0.21/0.55  % (12053)Time elapsed: 0.146 s
% 0.21/0.55  % (12053)------------------------------
% 0.21/0.55  % (12053)------------------------------
% 0.21/0.55  % (12050)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (12063)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (12057)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (12037)Refutation not found, incomplete strategy% (12037)------------------------------
% 0.21/0.56  % (12037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (12037)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (12037)Memory used [KB]: 11001
% 0.21/0.56  % (12037)Time elapsed: 0.153 s
% 0.21/0.56  % (12037)------------------------------
% 0.21/0.56  % (12037)------------------------------
% 0.21/0.56  % (12061)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (12055)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.15/0.66  % (12066)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.15/0.69  % (12067)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.67/0.73  % (12068)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.17/0.82  % (12040)Time limit reached!
% 3.17/0.82  % (12040)------------------------------
% 3.17/0.82  % (12040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.17/0.83  % (12040)Termination reason: Time limit
% 3.17/0.83  
% 3.17/0.83  % (12040)Memory used [KB]: 10234
% 3.17/0.83  % (12040)Time elapsed: 0.417 s
% 3.17/0.83  % (12040)------------------------------
% 3.17/0.83  % (12040)------------------------------
% 4.02/0.91  % (12047)Time limit reached!
% 4.02/0.91  % (12047)------------------------------
% 4.02/0.91  % (12047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.02/0.92  % (12047)Termination reason: Time limit
% 4.02/0.92  
% 4.02/0.92  % (12047)Memory used [KB]: 10874
% 4.02/0.92  % (12047)Time elapsed: 0.507 s
% 4.02/0.92  % (12047)------------------------------
% 4.02/0.92  % (12047)------------------------------
% 4.02/0.92  % (12045)Time limit reached!
% 4.02/0.92  % (12045)------------------------------
% 4.02/0.92  % (12045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.02/0.92  % (12045)Termination reason: Time limit
% 4.02/0.92  % (12045)Termination phase: Saturation
% 4.02/0.92  
% 4.02/0.92  % (12045)Memory used [KB]: 16119
% 4.02/0.92  % (12045)Time elapsed: 0.500 s
% 4.02/0.92  % (12035)Time limit reached!
% 4.02/0.92  % (12035)------------------------------
% 4.02/0.92  % (12035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.02/0.92  % (12045)------------------------------
% 4.02/0.92  % (12045)------------------------------
% 4.42/0.94  % (12035)Termination reason: Time limit
% 4.42/0.94  % (12035)Termination phase: Saturation
% 4.42/0.94  
% 4.42/0.94  % (12035)Memory used [KB]: 2686
% 4.42/0.94  % (12036)Time limit reached!
% 4.42/0.94  % (12036)------------------------------
% 4.42/0.94  % (12036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.42/0.94  % (12036)Termination reason: Time limit
% 4.42/0.94  
% 4.42/0.94  % (12036)Memory used [KB]: 9083
% 4.42/0.94  % (12036)Time elapsed: 0.524 s
% 4.42/0.94  % (12036)------------------------------
% 4.42/0.94  % (12036)------------------------------
% 4.42/0.94  % (12035)Time elapsed: 0.500 s
% 4.42/0.94  % (12035)------------------------------
% 4.42/0.94  % (12035)------------------------------
% 4.87/1.01  % (12052)Time limit reached!
% 4.87/1.01  % (12052)------------------------------
% 4.87/1.01  % (12052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.87/1.01  % (12052)Termination reason: Time limit
% 4.87/1.01  
% 4.87/1.01  % (12052)Memory used [KB]: 16886
% 4.87/1.01  % (12052)Time elapsed: 0.603 s
% 4.87/1.01  % (12052)------------------------------
% 4.87/1.01  % (12052)------------------------------
% 4.87/1.01  % (12064)Time limit reached!
% 4.87/1.01  % (12064)------------------------------
% 4.87/1.01  % (12064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.87/1.01  % (12064)Termination reason: Time limit
% 4.87/1.01  
% 4.87/1.01  % (12064)Memory used [KB]: 8315
% 4.87/1.01  % (12064)Time elapsed: 0.612 s
% 4.87/1.01  % (12064)------------------------------
% 4.87/1.01  % (12064)------------------------------
% 4.87/1.01  % (12069)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.87/1.02  % (12042)Time limit reached!
% 4.87/1.02  % (12042)------------------------------
% 4.87/1.02  % (12042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.87/1.02  % (12042)Termination reason: Time limit
% 4.87/1.02  % (12042)Termination phase: Saturation
% 4.87/1.02  
% 4.87/1.02  % (12042)Memory used [KB]: 11769
% 4.87/1.02  % (12042)Time elapsed: 0.600 s
% 4.87/1.02  % (12042)------------------------------
% 4.87/1.02  % (12042)------------------------------
% 4.87/1.03  % (12070)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.87/1.04  % (12072)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.87/1.06  % (12071)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.87/1.07  % (12073)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.58/1.14  % (12074)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 5.58/1.15  % (12075)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 5.58/1.16  % (12076)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 5.58/1.16  % (12074)Refutation not found, incomplete strategy% (12074)------------------------------
% 5.58/1.16  % (12074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.58/1.16  % (12074)Termination reason: Refutation not found, incomplete strategy
% 5.58/1.16  
% 5.58/1.16  % (12074)Memory used [KB]: 1791
% 5.58/1.16  % (12074)Time elapsed: 0.130 s
% 5.58/1.16  % (12074)------------------------------
% 5.58/1.16  % (12074)------------------------------
% 6.57/1.22  % (12057)Time limit reached!
% 6.57/1.22  % (12057)------------------------------
% 6.57/1.22  % (12057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.74/1.23  % (12057)Termination reason: Time limit
% 6.74/1.23  % (12057)Termination phase: Saturation
% 6.74/1.23  
% 6.74/1.23  % (12057)Memory used [KB]: 3198
% 6.74/1.23  % (12057)Time elapsed: 0.800 s
% 6.74/1.23  % (12057)------------------------------
% 6.74/1.23  % (12057)------------------------------
% 6.74/1.31  % (12077)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 6.74/1.31  % (12069)Time limit reached!
% 6.74/1.31  % (12069)------------------------------
% 6.74/1.31  % (12069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.74/1.32  % (12069)Termination reason: Time limit
% 6.74/1.32  
% 6.74/1.32  % (12069)Memory used [KB]: 7547
% 6.74/1.32  % (12069)Time elapsed: 0.432 s
% 6.74/1.32  % (12069)------------------------------
% 6.74/1.32  % (12069)------------------------------
% 7.53/1.36  % (12078)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 7.53/1.36  % (12070)Time limit reached!
% 7.53/1.36  % (12070)------------------------------
% 7.53/1.36  % (12070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.53/1.36  % (12070)Termination reason: Time limit
% 7.53/1.36  % (12070)Termination phase: Saturation
% 7.53/1.36  
% 7.53/1.36  % (12070)Memory used [KB]: 15351
% 7.53/1.36  % (12070)Time elapsed: 0.400 s
% 7.53/1.36  % (12070)------------------------------
% 7.53/1.36  % (12070)------------------------------
% 8.09/1.47  % (12079)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 8.09/1.47  % (12079)Refutation not found, incomplete strategy% (12079)------------------------------
% 8.09/1.47  % (12079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.09/1.47  % (12079)Termination reason: Refutation not found, incomplete strategy
% 8.09/1.47  
% 8.09/1.47  % (12079)Memory used [KB]: 1663
% 8.09/1.47  % (12079)Time elapsed: 0.117 s
% 8.09/1.47  % (12079)------------------------------
% 8.09/1.47  % (12079)------------------------------
% 8.61/1.50  % (12080)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 9.53/1.60  % (12081)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 9.53/1.61  % (12062)Time limit reached!
% 9.53/1.61  % (12062)------------------------------
% 9.53/1.61  % (12062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.53/1.61  % (12062)Termination reason: Time limit
% 9.53/1.61  % (12062)Termination phase: Saturation
% 9.53/1.61  
% 9.53/1.61  % (12062)Memory used [KB]: 17654
% 9.53/1.61  % (12062)Time elapsed: 1.200 s
% 9.53/1.61  % (12062)------------------------------
% 9.53/1.61  % (12062)------------------------------
% 9.74/1.66  % (12058)Time limit reached!
% 9.74/1.66  % (12058)------------------------------
% 9.74/1.66  % (12058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.74/1.66  % (12058)Termination reason: Time limit
% 9.74/1.66  
% 9.74/1.66  % (12058)Memory used [KB]: 15607
% 9.74/1.66  % (12058)Time elapsed: 1.218 s
% 9.74/1.66  % (12058)------------------------------
% 9.74/1.66  % (12058)------------------------------
% 9.74/1.72  % (12050)Time limit reached!
% 9.74/1.72  % (12050)------------------------------
% 9.74/1.72  % (12050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.74/1.72  % (12050)Termination reason: Time limit
% 9.74/1.72  
% 9.74/1.72  % (12050)Memory used [KB]: 19317
% 9.74/1.72  % (12050)Time elapsed: 1.310 s
% 9.74/1.72  % (12050)------------------------------
% 9.74/1.72  % (12050)------------------------------
% 10.42/1.74  % (12082)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 10.42/1.79  % (12078)Time limit reached!
% 10.42/1.79  % (12078)------------------------------
% 10.42/1.79  % (12078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.42/1.79  % (12078)Termination reason: Time limit
% 10.42/1.79  % (12078)Termination phase: Saturation
% 10.42/1.79  
% 10.42/1.79  % (12078)Memory used [KB]: 5756
% 10.42/1.79  % (12078)Time elapsed: 0.500 s
% 10.42/1.79  % (12078)------------------------------
% 10.42/1.79  % (12078)------------------------------
% 10.42/1.80  % (12060)Time limit reached!
% 10.42/1.80  % (12060)------------------------------
% 10.42/1.80  % (12060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.42/1.80  % (12060)Termination reason: Time limit
% 10.42/1.80  
% 10.42/1.80  % (12060)Memory used [KB]: 24690
% 10.42/1.80  % (12060)Time elapsed: 1.393 s
% 10.42/1.80  % (12060)------------------------------
% 10.42/1.80  % (12060)------------------------------
% 11.44/1.82  % (12083)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 11.44/1.84  % (12084)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 12.01/1.93  % (12085)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 12.01/1.97  % (12086)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 12.01/1.97  % (12039)Time limit reached!
% 12.01/1.97  % (12039)------------------------------
% 12.01/1.97  % (12039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.01/1.97  % (12039)Termination reason: Time limit
% 12.01/1.97  
% 12.01/1.97  % (12039)Memory used [KB]: 22643
% 12.01/1.97  % (12039)Time elapsed: 1.532 s
% 12.01/1.97  % (12039)------------------------------
% 12.01/1.97  % (12039)------------------------------
% 12.94/2.01  % (12063)Time limit reached!
% 12.94/2.01  % (12063)------------------------------
% 12.94/2.01  % (12063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.94/2.01  % (12063)Termination reason: Time limit
% 12.94/2.01  % (12063)Termination phase: Saturation
% 12.94/2.01  
% 12.94/2.01  % (12063)Memory used [KB]: 17910
% 12.94/2.01  % (12063)Time elapsed: 1.500 s
% 12.94/2.01  % (12063)------------------------------
% 12.94/2.01  % (12063)------------------------------
% 13.08/2.07  % (12046)Time limit reached!
% 13.08/2.07  % (12046)------------------------------
% 13.08/2.07  % (12046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.08/2.07  % (12046)Termination reason: Time limit
% 13.08/2.07  
% 13.08/2.07  % (12046)Memory used [KB]: 26353
% 13.08/2.07  % (12046)Time elapsed: 1.617 s
% 13.08/2.07  % (12046)------------------------------
% 13.08/2.07  % (12046)------------------------------
% 13.77/2.13  % (12087)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 13.77/2.13  % (12082)Time limit reached!
% 13.77/2.13  % (12082)------------------------------
% 13.77/2.13  % (12082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.77/2.13  % (12082)Termination reason: Time limit
% 13.77/2.13  % (12082)Termination phase: Saturation
% 13.77/2.13  
% 13.77/2.13  % (12082)Memory used [KB]: 5756
% 13.77/2.13  % (12082)Time elapsed: 0.400 s
% 13.77/2.13  % (12082)------------------------------
% 13.77/2.13  % (12082)------------------------------
% 13.77/2.14  % (12088)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 14.35/2.21  % (12089)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 14.35/2.21  % (12072)Time limit reached!
% 14.35/2.21  % (12072)------------------------------
% 14.35/2.21  % (12072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.35/2.21  % (12072)Termination reason: Time limit
% 14.35/2.21  
% 14.35/2.21  % (12072)Memory used [KB]: 19957
% 14.35/2.21  % (12072)Time elapsed: 1.223 s
% 14.35/2.21  % (12072)------------------------------
% 14.35/2.21  % (12072)------------------------------
% 14.35/2.25  % (12085)Time limit reached!
% 14.35/2.25  % (12085)------------------------------
% 14.35/2.25  % (12085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.35/2.25  % (12085)Termination reason: Time limit
% 14.35/2.25  
% 14.35/2.25  % (12085)Memory used [KB]: 4349
% 14.35/2.25  % (12085)Time elapsed: 0.425 s
% 14.35/2.25  % (12085)------------------------------
% 14.35/2.25  % (12085)------------------------------
% 14.35/2.27  % (12090)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 14.89/2.28  % (12049)Time limit reached!
% 14.89/2.28  % (12049)------------------------------
% 14.89/2.28  % (12049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.89/2.28  % (12049)Termination reason: Time limit
% 14.89/2.28  % (12049)Termination phase: Saturation
% 14.89/2.28  
% 14.89/2.28  % (12049)Memory used [KB]: 21364
% 14.89/2.28  % (12049)Time elapsed: 1.800 s
% 14.89/2.28  % (12049)------------------------------
% 14.89/2.28  % (12049)------------------------------
% 14.89/2.29  % (12091)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 14.89/2.30  % (12091)Refutation not found, incomplete strategy% (12091)------------------------------
% 14.89/2.30  % (12091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.89/2.30  % (12091)Termination reason: Refutation not found, incomplete strategy
% 14.89/2.30  
% 14.89/2.30  % (12091)Memory used [KB]: 6140
% 14.89/2.30  % (12091)Time elapsed: 0.047 s
% 14.89/2.30  % (12091)------------------------------
% 14.89/2.30  % (12091)------------------------------
% 14.89/2.33  % (12092)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 14.89/2.35  % (12092)Refutation not found, incomplete strategy% (12092)------------------------------
% 14.89/2.35  % (12092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.89/2.35  % (12092)Termination reason: Refutation not found, incomplete strategy
% 14.89/2.35  
% 14.89/2.35  % (12092)Memory used [KB]: 6268
% 14.89/2.35  % (12092)Time elapsed: 0.068 s
% 14.89/2.35  % (12092)------------------------------
% 14.89/2.35  % (12092)------------------------------
% 14.89/2.35  % (12068)Time limit reached!
% 14.89/2.35  % (12068)------------------------------
% 14.89/2.35  % (12068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.89/2.35  % (12068)Termination reason: Time limit
% 14.89/2.35  % (12068)Termination phase: Saturation
% 14.89/2.35  
% 14.89/2.35  % (12068)Memory used [KB]: 26353
% 14.89/2.35  % (12068)Time elapsed: 1.700 s
% 14.89/2.35  % (12068)------------------------------
% 14.89/2.35  % (12068)------------------------------
% 15.87/2.43  % (12093)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 15.87/2.43  % (12093)Refutation not found, incomplete strategy% (12093)------------------------------
% 15.87/2.43  % (12093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.87/2.43  % (12093)Termination reason: Refutation not found, incomplete strategy
% 15.87/2.43  
% 15.87/2.43  % (12093)Memory used [KB]: 10746
% 15.87/2.43  % (12093)Time elapsed: 0.068 s
% 15.87/2.43  % (12093)------------------------------
% 15.87/2.43  % (12093)------------------------------
% 15.87/2.51  % (12041)Time limit reached!
% 15.87/2.51  % (12041)------------------------------
% 15.87/2.51  % (12041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.87/2.51  % (12041)Termination reason: Time limit
% 15.87/2.51  
% 15.87/2.51  % (12041)Memory used [KB]: 36076
% 15.87/2.51  % (12041)Time elapsed: 2.073 s
% 15.87/2.51  % (12041)------------------------------
% 15.87/2.51  % (12041)------------------------------
% 15.87/2.52  % (12054)Time limit reached!
% 15.87/2.52  % (12054)------------------------------
% 15.87/2.52  % (12054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.20/2.53  % (12054)Termination reason: Time limit
% 17.20/2.53  % (12054)Termination phase: Saturation
% 17.20/2.53  
% 17.20/2.53  % (12054)Memory used [KB]: 38250
% 17.20/2.53  % (12054)Time elapsed: 2.0000 s
% 17.20/2.53  % (12054)------------------------------
% 17.20/2.53  % (12054)------------------------------
% 17.20/2.57  % (12090)Time limit reached!
% 17.20/2.57  % (12090)------------------------------
% 17.20/2.57  % (12090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.20/2.57  % (12090)Termination reason: Time limit
% 17.20/2.57  % (12090)Termination phase: Saturation
% 17.20/2.57  
% 17.20/2.57  % (12090)Memory used [KB]: 9850
% 17.20/2.57  % (12090)Time elapsed: 0.400 s
% 17.20/2.57  % (12090)------------------------------
% 17.20/2.57  % (12090)------------------------------
% 18.52/2.74  % (12081)Time limit reached!
% 18.52/2.74  % (12081)------------------------------
% 18.52/2.74  % (12081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.52/2.74  % (12081)Termination reason: Time limit
% 18.52/2.74  % (12081)Termination phase: Saturation
% 18.52/2.74  
% 18.52/2.74  % (12081)Memory used [KB]: 13176
% 18.52/2.74  % (12081)Time elapsed: 1.235 s
% 18.52/2.74  % (12081)------------------------------
% 18.52/2.74  % (12081)------------------------------
% 20.89/3.05  % (12055)Time limit reached!
% 20.89/3.05  % (12055)------------------------------
% 20.89/3.05  % (12055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.89/3.05  % (12055)Termination reason: Time limit
% 20.89/3.05  % (12055)Termination phase: Saturation
% 20.89/3.05  
% 20.89/3.05  % (12055)Memory used [KB]: 45415
% 20.89/3.05  % (12055)Time elapsed: 2.600 s
% 20.89/3.05  % (12055)------------------------------
% 20.89/3.05  % (12055)------------------------------
% 21.67/3.08  % (12084)Time limit reached!
% 21.67/3.08  % (12084)------------------------------
% 21.67/3.08  % (12084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.67/3.08  % (12084)Termination reason: Time limit
% 21.67/3.08  % (12084)Termination phase: Saturation
% 21.67/3.08  
% 21.67/3.08  % (12084)Memory used [KB]: 46054
% 21.67/3.08  % (12084)Time elapsed: 1.300 s
% 21.67/3.08  % (12084)------------------------------
% 21.67/3.08  % (12084)------------------------------
% 24.29/3.42  % (12048)Time limit reached!
% 24.29/3.42  % (12048)------------------------------
% 24.29/3.42  % (12048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.29/3.42  % (12048)Termination reason: Time limit
% 24.29/3.42  
% 24.29/3.42  % (12048)Memory used [KB]: 14711
% 24.29/3.42  % (12048)Time elapsed: 3.016 s
% 24.29/3.42  % (12048)------------------------------
% 24.29/3.42  % (12048)------------------------------
% 24.43/3.45  % (12067)Time limit reached!
% 24.43/3.45  % (12067)------------------------------
% 24.43/3.45  % (12067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.43/3.45  % (12067)Termination reason: Time limit
% 24.43/3.45  
% 24.43/3.45  % (12067)Memory used [KB]: 41065
% 24.43/3.45  % (12067)Time elapsed: 2.873 s
% 24.43/3.45  % (12067)------------------------------
% 24.43/3.45  % (12067)------------------------------
% 27.54/3.83  % (12056)Refutation not found, incomplete strategy% (12056)------------------------------
% 27.54/3.83  % (12056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 27.54/3.83  % (12056)Termination reason: Refutation not found, incomplete strategy
% 27.54/3.83  
% 27.54/3.83  % (12056)Memory used [KB]: 34668
% 27.54/3.83  % (12056)Time elapsed: 3.432 s
% 27.54/3.83  % (12056)------------------------------
% 27.54/3.83  % (12056)------------------------------
% 31.32/4.30  % (12065)Time limit reached!
% 31.32/4.30  % (12065)------------------------------
% 31.32/4.30  % (12065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.32/4.30  % (12065)Termination reason: Time limit
% 31.32/4.30  % (12065)Termination phase: Saturation
% 31.32/4.30  
% 31.32/4.30  % (12065)Memory used [KB]: 61534
% 31.32/4.30  % (12065)Time elapsed: 3.900 s
% 31.32/4.30  % (12065)------------------------------
% 31.32/4.30  % (12065)------------------------------
% 32.77/4.51  % (12077)Refutation found. Thanks to Tanya!
% 32.77/4.51  % SZS status Theorem for theBenchmark
% 32.77/4.52  % SZS output start Proof for theBenchmark
% 32.77/4.52  fof(f22535,plain,(
% 32.77/4.52    $false),
% 32.77/4.52    inference(subsumption_resolution,[],[f22438,f81])).
% 32.77/4.52  fof(f81,plain,(
% 32.77/4.52    ( ! [X2,X0,X5] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X5,X2))) )),
% 32.77/4.52    inference(equality_resolution,[],[f80])).
% 32.77/4.52  fof(f80,plain,(
% 32.77/4.52    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 32.77/4.52    inference(equality_resolution,[],[f72])).
% 32.77/4.52  fof(f72,plain,(
% 32.77/4.52    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 32.77/4.52    inference(definition_unfolding,[],[f52,f62])).
% 32.77/4.52  fof(f62,plain,(
% 32.77/4.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 32.77/4.52    inference(definition_unfolding,[],[f41,f61])).
% 32.77/4.52  fof(f61,plain,(
% 32.77/4.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 32.77/4.52    inference(definition_unfolding,[],[f49,f60])).
% 32.77/4.52  fof(f60,plain,(
% 32.77/4.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 32.77/4.52    inference(definition_unfolding,[],[f58,f59])).
% 32.77/4.52  fof(f59,plain,(
% 32.77/4.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 32.77/4.52    inference(cnf_transformation,[],[f13])).
% 32.77/4.52  fof(f13,axiom,(
% 32.77/4.52    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 32.77/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 32.77/4.52  fof(f58,plain,(
% 32.77/4.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 32.77/4.52    inference(cnf_transformation,[],[f12])).
% 32.77/4.52  fof(f12,axiom,(
% 32.77/4.52    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 32.77/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 32.77/4.52  fof(f49,plain,(
% 32.77/4.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 32.77/4.52    inference(cnf_transformation,[],[f11])).
% 32.77/4.52  fof(f11,axiom,(
% 32.77/4.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 32.77/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 32.77/4.52  fof(f41,plain,(
% 32.77/4.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 32.77/4.52    inference(cnf_transformation,[],[f10])).
% 32.77/4.52  fof(f10,axiom,(
% 32.77/4.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 32.77/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 32.77/4.52  fof(f52,plain,(
% 32.77/4.52    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 32.77/4.52    inference(cnf_transformation,[],[f31])).
% 32.77/4.52  fof(f31,plain,(
% 32.77/4.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 32.77/4.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 32.77/4.52  fof(f30,plain,(
% 32.77/4.52    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 32.77/4.52    introduced(choice_axiom,[])).
% 32.77/4.53  fof(f29,plain,(
% 32.77/4.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 32.77/4.53    inference(rectify,[],[f28])).
% 32.77/4.53  fof(f28,plain,(
% 32.77/4.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 32.77/4.53    inference(flattening,[],[f27])).
% 32.77/4.53  fof(f27,plain,(
% 32.77/4.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 32.77/4.53    inference(nnf_transformation,[],[f17])).
% 32.77/4.53  fof(f17,plain,(
% 32.77/4.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 32.77/4.53    inference(ennf_transformation,[],[f8])).
% 32.77/4.53  fof(f8,axiom,(
% 32.77/4.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 32.77/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 32.77/4.53  fof(f22438,plain,(
% 32.77/4.53    ~r2_hidden(sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 32.77/4.53    inference(superposition,[],[f9572,f22290])).
% 32.77/4.53  fof(f22290,plain,(
% 32.77/4.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 32.77/4.53    inference(subsumption_resolution,[],[f22164,f9573])).
% 32.77/4.53  fof(f9573,plain,(
% 32.77/4.53    ~r2_hidden(sK0,sK2)),
% 32.77/4.53    inference(subsumption_resolution,[],[f9561,f5665])).
% 32.77/4.53  fof(f5665,plain,(
% 32.77/4.53    r2_hidden(sK1,sK2)),
% 32.77/4.53    inference(duplicate_literal_removal,[],[f5622])).
% 32.77/4.53  fof(f5622,plain,(
% 32.77/4.53    r2_hidden(sK1,sK2) | r2_hidden(sK1,sK2)),
% 32.77/4.53    inference(resolution,[],[f5444,f79])).
% 32.77/4.53  fof(f79,plain,(
% 32.77/4.53    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5))) )),
% 32.77/4.53    inference(equality_resolution,[],[f78])).
% 32.77/4.53  fof(f78,plain,(
% 32.77/4.53    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 32.77/4.53    inference(equality_resolution,[],[f71])).
% 32.77/4.53  fof(f71,plain,(
% 32.77/4.53    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 32.77/4.53    inference(definition_unfolding,[],[f53,f62])).
% 32.77/4.53  fof(f53,plain,(
% 32.77/4.53    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 32.77/4.53    inference(cnf_transformation,[],[f31])).
% 32.77/4.53  fof(f5444,plain,(
% 32.77/4.53    ( ! [X32] : (~r2_hidden(X32,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | r2_hidden(X32,sK2) | r2_hidden(sK1,sK2)) )),
% 32.77/4.53    inference(superposition,[],[f77,f4957])).
% 32.77/4.53  fof(f4957,plain,(
% 32.77/4.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | r2_hidden(sK1,sK2)),
% 32.77/4.53    inference(duplicate_literal_removal,[],[f4895])).
% 32.77/4.53  fof(f4895,plain,(
% 32.77/4.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | r2_hidden(sK1,sK2) | r2_hidden(sK1,sK2)),
% 32.77/4.53    inference(superposition,[],[f201,f4836])).
% 32.77/4.53  fof(f4836,plain,(
% 32.77/4.53    ( ! [X6] : (k5_xboole_0(k1_xboole_0,X6) = X6 | r2_hidden(sK1,sK2)) )),
% 32.77/4.53    inference(forward_demodulation,[],[f4791,f36])).
% 32.77/4.53  fof(f36,plain,(
% 32.77/4.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 32.77/4.53    inference(cnf_transformation,[],[f5])).
% 32.77/4.53  fof(f5,axiom,(
% 32.77/4.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 32.77/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 32.77/4.53  fof(f4791,plain,(
% 32.77/4.53    ( ! [X6] : (k5_xboole_0(X6,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X6,k1_xboole_0)) | r2_hidden(sK1,sK2)) )),
% 32.77/4.53    inference(superposition,[],[f4725,f38])).
% 32.77/4.53  fof(f38,plain,(
% 32.77/4.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 32.77/4.53    inference(cnf_transformation,[],[f2])).
% 32.77/4.53  fof(f2,axiom,(
% 32.77/4.53    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 32.77/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 32.77/4.53  fof(f4725,plain,(
% 32.77/4.53    ( ! [X18] : (k5_xboole_0(k1_xboole_0,X18) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X18)) | r2_hidden(sK1,sK2)) )),
% 32.77/4.53    inference(duplicate_literal_removal,[],[f4689])).
% 32.77/4.53  fof(f4689,plain,(
% 32.77/4.53    ( ! [X18] : (k5_xboole_0(k1_xboole_0,X18) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X18)) | r2_hidden(sK1,sK2) | r2_hidden(sK1,sK2)) )),
% 32.77/4.53    inference(superposition,[],[f3365,f3226])).
% 32.77/4.53  fof(f3226,plain,(
% 32.77/4.53    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X0)) | r2_hidden(sK1,sK2)) )),
% 32.77/4.53    inference(superposition,[],[f2852,f38])).
% 32.77/4.53  fof(f2852,plain,(
% 32.77/4.53    ( ! [X9] : (k5_xboole_0(k1_xboole_0,X9) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X9,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | r2_hidden(sK1,sK2)) )),
% 32.77/4.53    inference(forward_demodulation,[],[f2843,f36])).
% 32.77/4.53  fof(f2843,plain,(
% 32.77/4.53    ( ! [X9] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X9,k1_xboole_0)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X9,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | r2_hidden(sK1,sK2)) )),
% 32.77/4.53    inference(duplicate_literal_removal,[],[f2787])).
% 32.77/4.53  fof(f2787,plain,(
% 32.77/4.53    ( ! [X9] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X9,k1_xboole_0)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X9,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | r2_hidden(sK1,sK2) | r2_hidden(sK1,sK2)) )),
% 32.77/4.53    inference(superposition,[],[f504,f201])).
% 32.77/4.53  fof(f504,plain,(
% 32.77/4.53    ( ! [X2,X3] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) | r2_hidden(sK1,sK2)) )),
% 32.77/4.53    inference(superposition,[],[f194,f42])).
% 32.77/4.53  fof(f42,plain,(
% 32.77/4.53    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 32.77/4.53    inference(cnf_transformation,[],[f6])).
% 32.77/4.53  fof(f6,axiom,(
% 32.77/4.53    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 32.77/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 32.77/4.53  fof(f194,plain,(
% 32.77/4.53    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X0,k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | r2_hidden(sK1,sK2)) )),
% 32.77/4.53    inference(superposition,[],[f95,f38])).
% 32.77/4.53  fof(f95,plain,(
% 32.77/4.53    ( ! [X0] : (k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0)) = k5_xboole_0(k1_xboole_0,X0) | r2_hidden(sK1,sK2)) )),
% 32.77/4.53    inference(superposition,[],[f42,f86])).
% 32.77/4.53  fof(f86,plain,(
% 32.77/4.53    k1_xboole_0 = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | r2_hidden(sK1,sK2)),
% 32.77/4.53    inference(forward_demodulation,[],[f65,f37])).
% 32.77/4.53  fof(f37,plain,(
% 32.77/4.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 32.77/4.53    inference(cnf_transformation,[],[f1])).
% 32.77/4.53  fof(f1,axiom,(
% 32.77/4.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 32.77/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 32.77/4.53  fof(f65,plain,(
% 32.77/4.53    r2_hidden(sK1,sK2) | k1_xboole_0 = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))),
% 32.77/4.53    inference(definition_unfolding,[],[f33,f40,f63])).
% 32.77/4.53  fof(f63,plain,(
% 32.77/4.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 32.77/4.53    inference(definition_unfolding,[],[f39,f62])).
% 32.77/4.53  fof(f39,plain,(
% 32.77/4.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 32.77/4.53    inference(cnf_transformation,[],[f9])).
% 32.77/4.53  fof(f9,axiom,(
% 32.77/4.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 32.77/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 32.77/4.53  fof(f40,plain,(
% 32.77/4.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 32.77/4.53    inference(cnf_transformation,[],[f4])).
% 32.77/4.53  fof(f4,axiom,(
% 32.77/4.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 32.77/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 32.77/4.53  fof(f33,plain,(
% 32.77/4.53    r2_hidden(sK1,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 32.77/4.53    inference(cnf_transformation,[],[f21])).
% 32.77/4.53  fof(f21,plain,(
% 32.77/4.53    (~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 32.77/4.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).
% 32.77/4.53  fof(f20,plain,(
% 32.77/4.53    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 32.77/4.53    introduced(choice_axiom,[])).
% 32.77/4.53  fof(f19,plain,(
% 32.77/4.53    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 32.77/4.53    inference(flattening,[],[f18])).
% 32.77/4.53  fof(f18,plain,(
% 32.77/4.53    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 32.77/4.53    inference(nnf_transformation,[],[f16])).
% 32.77/4.53  fof(f16,plain,(
% 32.77/4.53    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 32.77/4.53    inference(ennf_transformation,[],[f15])).
% 32.77/4.53  fof(f15,negated_conjecture,(
% 32.77/4.53    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 32.77/4.53    inference(negated_conjecture,[],[f14])).
% 32.77/4.53  fof(f14,conjecture,(
% 32.77/4.53    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 32.77/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 32.77/4.53  fof(f3365,plain,(
% 32.77/4.53    ( ! [X0] : (k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X0)) | r2_hidden(sK1,sK2)) )),
% 32.77/4.53    inference(superposition,[],[f2854,f38])).
% 32.77/4.53  fof(f2854,plain,(
% 32.77/4.53    ( ! [X11] : (k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X11) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X11,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | r2_hidden(sK1,sK2)) )),
% 32.77/4.53    inference(forward_demodulation,[],[f2842,f36])).
% 32.77/4.53  fof(f2842,plain,(
% 32.77/4.53    ( ! [X11] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X11,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X11,k1_xboole_0)) | r2_hidden(sK1,sK2)) )),
% 32.77/4.53    inference(duplicate_literal_removal,[],[f2789])).
% 32.77/4.53  fof(f2789,plain,(
% 32.77/4.53    ( ! [X11] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X11,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X11,k1_xboole_0)) | r2_hidden(sK1,sK2) | r2_hidden(sK1,sK2)) )),
% 32.77/4.53    inference(superposition,[],[f504,f86])).
% 32.77/4.53  fof(f201,plain,(
% 32.77/4.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | r2_hidden(sK1,sK2)),
% 32.77/4.53    inference(forward_demodulation,[],[f192,f36])).
% 32.77/4.53  fof(f192,plain,(
% 32.77/4.53    k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k1_xboole_0) | r2_hidden(sK1,sK2)),
% 32.77/4.53    inference(superposition,[],[f95,f35])).
% 32.77/4.53  fof(f35,plain,(
% 32.77/4.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 32.77/4.53    inference(cnf_transformation,[],[f7])).
% 32.77/4.53  fof(f7,axiom,(
% 32.77/4.53    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 32.77/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 32.77/4.53  fof(f77,plain,(
% 32.77/4.53    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 32.77/4.53    inference(equality_resolution,[],[f43])).
% 32.77/4.53  fof(f43,plain,(
% 32.77/4.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 32.77/4.53    inference(cnf_transformation,[],[f26])).
% 32.77/4.53  fof(f26,plain,(
% 32.77/4.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 32.77/4.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 32.77/4.53  fof(f25,plain,(
% 32.77/4.53    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 32.77/4.53    introduced(choice_axiom,[])).
% 32.77/4.53  fof(f24,plain,(
% 32.77/4.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 32.77/4.53    inference(rectify,[],[f23])).
% 32.77/4.53  fof(f23,plain,(
% 32.77/4.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 32.77/4.53    inference(flattening,[],[f22])).
% 32.77/4.53  fof(f22,plain,(
% 32.77/4.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 32.77/4.53    inference(nnf_transformation,[],[f3])).
% 32.77/4.53  fof(f3,axiom,(
% 32.77/4.53    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 32.77/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 32.77/4.53  fof(f9561,plain,(
% 32.77/4.53    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2)),
% 32.77/4.53    inference(duplicate_literal_removal,[],[f9493])).
% 32.77/4.53  fof(f9493,plain,(
% 32.77/4.53    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2)),
% 32.77/4.53    inference(superposition,[],[f1945,f7717])).
% 32.77/4.53  fof(f7717,plain,(
% 32.77/4.53    sK0 = sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK0,sK2)),
% 32.77/4.53    inference(subsumption_resolution,[],[f7708,f5665])).
% 32.77/4.53  fof(f7708,plain,(
% 32.77/4.53    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | sK0 = sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 32.77/4.53    inference(duplicate_literal_removal,[],[f7652])).
% 32.77/4.53  fof(f7652,plain,(
% 32.77/4.53    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | sK0 = sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 32.77/4.53    inference(superposition,[],[f1945,f7622])).
% 32.77/4.53  fof(f7622,plain,(
% 32.77/4.53    sK1 = sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK0,sK2) | sK0 = sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 32.77/4.53    inference(subsumption_resolution,[],[f768,f5665])).
% 32.77/4.53  fof(f768,plain,(
% 32.77/4.53    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2) | sK1 = sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK0 = sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 32.77/4.53    inference(duplicate_literal_removal,[],[f760])).
% 32.77/4.53  fof(f760,plain,(
% 32.77/4.53    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2) | sK1 = sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK0 = sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK0 = sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 32.77/4.53    inference(resolution,[],[f375,f84])).
% 32.77/4.53  fof(f84,plain,(
% 32.77/4.53    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) )),
% 32.77/4.53    inference(equality_resolution,[],[f74])).
% 32.77/4.53  fof(f74,plain,(
% 32.77/4.53    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 32.77/4.53    inference(definition_unfolding,[],[f50,f62])).
% 32.77/4.53  fof(f50,plain,(
% 32.77/4.53    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 32.77/4.53    inference(cnf_transformation,[],[f31])).
% 32.77/4.53  fof(f375,plain,(
% 32.77/4.53    r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2)),
% 32.77/4.53    inference(trivial_inequality_removal,[],[f374])).
% 32.77/4.53  fof(f374,plain,(
% 32.77/4.53    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 32.77/4.53    inference(duplicate_literal_removal,[],[f370])).
% 32.77/4.53  fof(f370,plain,(
% 32.77/4.53    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 32.77/4.53    inference(superposition,[],[f127,f35])).
% 32.77/4.53  fof(f127,plain,(
% 32.77/4.53    ( ! [X1] : (k1_xboole_0 != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X1) | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X1),X1)) )),
% 32.77/4.53    inference(superposition,[],[f85,f47])).
% 32.77/4.53  fof(f47,plain,(
% 32.77/4.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 32.77/4.53    inference(cnf_transformation,[],[f26])).
% 32.77/4.53  fof(f85,plain,(
% 32.77/4.53    k1_xboole_0 != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2)),
% 32.77/4.53    inference(forward_demodulation,[],[f64,f37])).
% 32.77/4.53  fof(f64,plain,(
% 32.77/4.53    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))),
% 32.77/4.53    inference(definition_unfolding,[],[f34,f40,f63])).
% 32.77/4.53  fof(f34,plain,(
% 32.77/4.53    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 32.77/4.53    inference(cnf_transformation,[],[f21])).
% 32.77/4.53  fof(f1945,plain,(
% 32.77/4.53    ~r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2) | ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2)),
% 32.77/4.53    inference(subsumption_resolution,[],[f439,f375])).
% 32.77/4.53  fof(f439,plain,(
% 32.77/4.53    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2)),
% 32.77/4.53    inference(trivial_inequality_removal,[],[f438])).
% 32.77/4.53  fof(f438,plain,(
% 32.77/4.53    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2)),
% 32.77/4.53    inference(duplicate_literal_removal,[],[f434])).
% 32.77/4.53  fof(f434,plain,(
% 32.77/4.53    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2) | ~r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 32.77/4.53    inference(superposition,[],[f128,f35])).
% 32.77/4.53  fof(f128,plain,(
% 32.77/4.53    ( ! [X2] : (k1_xboole_0 != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X2) | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X2),sK2) | ~r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),X2),X2)) )),
% 32.77/4.53    inference(superposition,[],[f85,f48])).
% 32.77/4.53  fof(f48,plain,(
% 32.77/4.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 32.77/4.53    inference(cnf_transformation,[],[f26])).
% 32.77/4.53  fof(f22164,plain,(
% 32.77/4.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | r2_hidden(sK0,sK2)),
% 32.77/4.53    inference(backward_demodulation,[],[f231,f22035])).
% 32.77/4.53  fof(f22035,plain,(
% 32.77/4.53    ( ! [X22] : (k5_xboole_0(k1_xboole_0,X22) = X22) )),
% 32.77/4.53    inference(forward_demodulation,[],[f21955,f36])).
% 32.77/4.53  fof(f21955,plain,(
% 32.77/4.53    ( ! [X22] : (k5_xboole_0(X22,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X22,k1_xboole_0))) )),
% 32.77/4.53    inference(superposition,[],[f21625,f38])).
% 32.77/4.53  fof(f21625,plain,(
% 32.77/4.53    ( ! [X39] : (k5_xboole_0(k1_xboole_0,X39) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X39))) )),
% 32.77/4.53    inference(superposition,[],[f21441,f36])).
% 32.77/4.53  fof(f21441,plain,(
% 32.77/4.53    ( ! [X4,X5] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X4,X5)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X5,X4))) )),
% 32.77/4.53    inference(subsumption_resolution,[],[f21271,f9573])).
% 32.77/4.53  fof(f21271,plain,(
% 32.77/4.53    ( ! [X4,X5] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X4,X5)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X5,X4)) | r2_hidden(sK0,sK2)) )),
% 32.77/4.53    inference(backward_demodulation,[],[f553,f21270])).
% 32.77/4.53  fof(f21270,plain,(
% 32.77/4.53    ( ! [X4,X3] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X3)))) )),
% 32.77/4.53    inference(subsumption_resolution,[],[f3061,f9573])).
% 32.77/4.53  fof(f3061,plain,(
% 32.77/4.53    ( ! [X4,X3] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X3))) | r2_hidden(sK0,sK2)) )),
% 32.77/4.53    inference(forward_demodulation,[],[f2996,f42])).
% 32.77/4.53  fof(f2996,plain,(
% 32.77/4.53    ( ! [X4,X3] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(X4,k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),X3)) | r2_hidden(sK0,sK2)) )),
% 32.77/4.53    inference(superposition,[],[f534,f38])).
% 32.77/4.53  fof(f534,plain,(
% 32.77/4.53    ( ! [X2,X3] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) | r2_hidden(sK0,sK2)) )),
% 32.77/4.53    inference(superposition,[],[f224,f42])).
% 32.77/4.53  fof(f224,plain,(
% 32.77/4.53    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X0,k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | r2_hidden(sK0,sK2)) )),
% 32.77/4.53    inference(superposition,[],[f117,f38])).
% 32.77/4.53  fof(f117,plain,(
% 32.77/4.53    ( ! [X0] : (k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0)) = k5_xboole_0(k1_xboole_0,X0) | r2_hidden(sK0,sK2)) )),
% 32.77/4.53    inference(superposition,[],[f42,f87])).
% 32.77/4.53  fof(f87,plain,(
% 32.77/4.53    k1_xboole_0 = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | r2_hidden(sK0,sK2)),
% 32.77/4.53    inference(forward_demodulation,[],[f66,f37])).
% 32.77/4.53  fof(f66,plain,(
% 32.77/4.53    r2_hidden(sK0,sK2) | k1_xboole_0 = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))),
% 32.77/4.53    inference(definition_unfolding,[],[f32,f40,f63])).
% 32.77/4.53  fof(f32,plain,(
% 32.77/4.53    r2_hidden(sK0,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 32.77/4.53    inference(cnf_transformation,[],[f21])).
% 32.77/4.53  fof(f553,plain,(
% 32.77/4.53    ( ! [X4,X5] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X4,X5)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X5))) | r2_hidden(sK0,sK2)) )),
% 32.77/4.53    inference(forward_demodulation,[],[f552,f42])).
% 32.77/4.53  fof(f552,plain,(
% 32.77/4.53    ( ! [X4,X5] : (k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(X4,k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),X5)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X4,X5)) | r2_hidden(sK0,sK2)) )),
% 32.77/4.53    inference(forward_demodulation,[],[f542,f42])).
% 32.77/4.53  fof(f542,plain,(
% 32.77/4.53    ( ! [X4,X5] : (k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(X4,k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),X5)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X4),X5) | r2_hidden(sK0,sK2)) )),
% 32.77/4.53    inference(superposition,[],[f42,f224])).
% 32.77/4.53  fof(f231,plain,(
% 32.77/4.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | r2_hidden(sK0,sK2)),
% 32.77/4.53    inference(forward_demodulation,[],[f222,f36])).
% 32.77/4.53  fof(f222,plain,(
% 32.77/4.53    k5_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k1_xboole_0) | r2_hidden(sK0,sK2)),
% 32.77/4.53    inference(superposition,[],[f117,f35])).
% 32.77/4.53  fof(f9572,plain,(
% 32.77/4.53    ( ! [X1] : (~r2_hidden(sK0,k3_xboole_0(sK2,X1))) )),
% 32.77/4.53    inference(subsumption_resolution,[],[f9571,f77])).
% 32.77/4.53  fof(f9571,plain,(
% 32.77/4.53    ( ! [X1] : (~r2_hidden(sK0,k3_xboole_0(sK2,X1)) | ~r2_hidden(sK0,sK2)) )),
% 32.77/4.53    inference(subsumption_resolution,[],[f9562,f5665])).
% 32.77/4.53  fof(f9562,plain,(
% 32.77/4.53    ( ! [X1] : (~r2_hidden(sK0,k3_xboole_0(sK2,X1)) | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2)) )),
% 32.77/4.53    inference(duplicate_literal_removal,[],[f9492])).
% 32.77/4.53  fof(f9492,plain,(
% 32.77/4.53    ( ! [X1] : (~r2_hidden(sK0,k3_xboole_0(sK2,X1)) | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r2_hidden(sK0,sK2)) )),
% 32.77/4.53    inference(superposition,[],[f1959,f7717])).
% 32.77/4.53  fof(f1959,plain,(
% 32.77/4.53    ( ! [X0] : (~r2_hidden(sK3(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_xboole_0(sK2,X0)) | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2)) )),
% 32.77/4.53    inference(resolution,[],[f1945,f77])).
% 32.77/4.53  % SZS output end Proof for theBenchmark
% 32.77/4.53  % (12077)------------------------------
% 32.77/4.53  % (12077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 32.77/4.53  % (12077)Termination reason: Refutation
% 32.77/4.53  
% 32.77/4.53  % (12077)Memory used [KB]: 14200
% 32.77/4.53  % (12077)Time elapsed: 3.319 s
% 32.77/4.53  % (12077)------------------------------
% 32.77/4.53  % (12077)------------------------------
% 32.77/4.53  % (12034)Success in time 4.18 s
%------------------------------------------------------------------------------
