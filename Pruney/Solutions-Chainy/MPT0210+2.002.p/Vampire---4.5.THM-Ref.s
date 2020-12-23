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
% DateTime   : Thu Dec  3 12:34:42 EST 2020

% Result     : Theorem 7.47s
% Output     : Refutation 8.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 318 expanded)
%              Number of leaves         :   10 (  88 expanded)
%              Depth                    :   27
%              Number of atoms          :  335 (1770 expanded)
%              Number of equality atoms :  177 (1189 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2915,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f24,f23,f23,f2897,f70])).

fof(f70,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f36,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).

fof(f21,plain,(
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

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f2897,plain,(
    r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f2896,f23])).

fof(f2896,plain,
    ( r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK2))
    | sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f2888])).

fof(f2888,plain,
    ( r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK2))
    | sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1 ),
    inference(resolution,[],[f2880,f70])).

fof(f2880,plain,
    ( r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f2879,f24])).

fof(f2879,plain,
    ( r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK2))
    | r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 = sK2 ),
    inference(duplicate_literal_removal,[],[f2871])).

fof(f2871,plain,
    ( r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK2))
    | r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 = sK2
    | sK0 = sK2
    | sK0 = sK2 ),
    inference(resolution,[],[f2811,f70])).

fof(f2811,plain,
    ( r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK2))
    | r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f2761,f65])).

fof(f65,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f39,f29])).

fof(f39,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2761,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK2))
    | r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f166,f2714])).

fof(f2714,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))
    | r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f2713,f67])).

fof(f67,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k2_enumset1(X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f38,f29])).

fof(f38,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2713,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK0,sK0,sK1,sK2))
    | r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f2665,f67])).

fof(f2665,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ r2_hidden(sK1,k2_enumset1(sK0,sK0,sK1,sK2))
    | r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(superposition,[],[f186,f2615])).

fof(f2615,plain,
    ( sK1 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))
    | r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f2614,f65])).

fof(f2614,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK0,sK0,sK1,sK2))
    | r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK1 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f2566,f65])).

fof(f2566,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ r2_hidden(sK2,k2_enumset1(sK0,sK0,sK1,sK2))
    | r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK1 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(superposition,[],[f186,f1286])).

fof(f1286,plain,
    ( sK2 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))
    | sK1 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f1269])).

fof(f1269,plain,
    ( sK2 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))
    | sK1 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))
    | sK2 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))
    | sK1 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(resolution,[],[f339,f70])).

fof(f339,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK0,sK0,sK1,sK2))
    | sK2 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))
    | sK1 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f322])).

fof(f322,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK0,sK0,sK1,sK2))
    | sK2 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))
    | sK1 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))
    | sK1 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(resolution,[],[f157,f70])).

fof(f157,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK1,sK1,sK1,sK2))
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK0,sK0,sK1,sK2)) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( k2_enumset1(sK1,sK1,sK1,sK2) != X0
      | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),X0),k2_enumset1(sK0,sK0,sK1,sK2))
      | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),X0),X0) ) ),
    inference(superposition,[],[f46,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f33,f28])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f46,plain,(
    k5_xboole_0(k2_enumset1(sK0,sK0,sK1,sK2),k3_xboole_0(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0))) != k2_enumset1(sK1,sK1,sK1,sK2) ),
    inference(definition_unfolding,[],[f25,f28,f29,f45,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f27,f29])).

fof(f27,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f44])).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f25,plain,(
    k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2)
    & sK0 != sK2
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 )
   => ( k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2)
      & sK0 != sK2
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
      & X0 != X2
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
          & X0 != X2
          & X0 != X1 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_enumset1)).

fof(f186,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK0,sK0,sK1,sK2))
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2] :
      ( k2_enumset1(sK1,sK1,sK1,sK2) != X2
      | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),X2),k2_enumset1(sK0,sK0,sK0,sK0))
      | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),X2),k2_enumset1(sK0,sK0,sK1,sK2))
      | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),X2),X2) ) ),
    inference(superposition,[],[f46,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f35,f28])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f166,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK0,sK0,sK0,sK0))
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X1] :
      ( k2_enumset1(sK1,sK1,sK1,sK2) != X1
      | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),X1),k2_enumset1(sK0,sK0,sK0,sK0))
      | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),X1),X1) ) ),
    inference(superposition,[],[f46,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f34,f28])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f23,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : run_vampire %s %d
% 0.07/0.25  % Computer   : n006.cluster.edu
% 0.07/0.25  % Model      : x86_64 x86_64
% 0.07/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.25  % Memory     : 8042.1875MB
% 0.07/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.25  % CPULimit   : 60
% 0.07/0.25  % WCLimit    : 600
% 0.07/0.25  % DateTime   : Tue Dec  1 12:38:37 EST 2020
% 0.07/0.25  % CPUTime    : 
% 0.11/0.33  % (28736)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.11/0.34  % (28739)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.11/0.35  % (28756)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.11/0.35  % (28735)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.11/0.35  % (28748)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.11/0.35  % (28734)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.11/0.35  % (28733)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.11/0.35  % (28733)Refutation not found, incomplete strategy% (28733)------------------------------
% 0.11/0.35  % (28733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.35  % (28733)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.35  
% 0.11/0.35  % (28733)Memory used [KB]: 1663
% 0.11/0.35  % (28733)Time elapsed: 0.065 s
% 0.11/0.35  % (28733)------------------------------
% 0.11/0.35  % (28733)------------------------------
% 0.11/0.36  % (28740)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.11/0.36  % (28738)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.11/0.36  % (28751)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.11/0.36  % (28752)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.11/0.36  % (28737)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.11/0.37  % (28749)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.11/0.37  % (28744)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.11/0.37  % (28755)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.11/0.37  % (28747)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.11/0.38  % (28735)Refutation not found, incomplete strategy% (28735)------------------------------
% 0.11/0.38  % (28735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.38  % (28735)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.38  
% 0.11/0.38  % (28735)Memory used [KB]: 10618
% 0.11/0.38  % (28735)Time elapsed: 0.088 s
% 0.11/0.38  % (28735)------------------------------
% 0.11/0.38  % (28735)------------------------------
% 0.11/0.38  % (28743)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.11/0.38  % (28741)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.11/0.38  % (28743)Refutation not found, incomplete strategy% (28743)------------------------------
% 0.11/0.38  % (28743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.38  % (28743)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.38  
% 0.11/0.38  % (28743)Memory used [KB]: 10618
% 0.11/0.38  % (28743)Time elapsed: 0.084 s
% 0.11/0.38  % (28743)------------------------------
% 0.11/0.38  % (28743)------------------------------
% 0.11/0.38  % (28745)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.11/0.38  % (28758)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.11/0.38  % (28760)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.11/0.38  % (28761)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.11/0.38  % (28741)Refutation not found, incomplete strategy% (28741)------------------------------
% 0.11/0.38  % (28741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.38  % (28741)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.38  
% 0.11/0.38  % (28741)Memory used [KB]: 10618
% 0.11/0.38  % (28741)Time elapsed: 0.097 s
% 0.11/0.38  % (28741)------------------------------
% 0.11/0.38  % (28741)------------------------------
% 0.11/0.39  % (28754)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.11/0.39  % (28754)Refutation not found, incomplete strategy% (28754)------------------------------
% 0.11/0.39  % (28754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.39  % (28754)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.39  
% 0.11/0.39  % (28754)Memory used [KB]: 1663
% 0.11/0.39  % (28754)Time elapsed: 0.097 s
% 0.11/0.39  % (28754)------------------------------
% 0.11/0.39  % (28754)------------------------------
% 0.11/0.39  % (28753)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.11/0.39  % (28753)Refutation not found, incomplete strategy% (28753)------------------------------
% 0.11/0.39  % (28753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.39  % (28753)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.39  
% 0.11/0.39  % (28753)Memory used [KB]: 10746
% 0.11/0.39  % (28753)Time elapsed: 0.096 s
% 0.11/0.39  % (28753)------------------------------
% 0.11/0.39  % (28753)------------------------------
% 0.11/0.39  % (28762)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.11/0.39  % (28744)Refutation not found, incomplete strategy% (28744)------------------------------
% 0.11/0.39  % (28744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.39  % (28744)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.39  
% 0.11/0.39  % (28744)Memory used [KB]: 10618
% 0.11/0.39  % (28744)Time elapsed: 0.107 s
% 0.11/0.39  % (28744)------------------------------
% 0.11/0.39  % (28744)------------------------------
% 0.11/0.39  % (28746)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.11/0.39  % (28750)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.11/0.40  % (28759)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.11/0.40  % (28742)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.11/0.40  % (28757)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.11/0.40  % (28742)Refutation not found, incomplete strategy% (28742)------------------------------
% 0.11/0.40  % (28742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.40  % (28742)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.40  
% 0.11/0.40  % (28742)Memory used [KB]: 10618
% 0.11/0.40  % (28742)Time elapsed: 0.102 s
% 0.11/0.40  % (28742)------------------------------
% 0.11/0.40  % (28742)------------------------------
% 0.11/0.40  % (28750)Refutation not found, incomplete strategy% (28750)------------------------------
% 0.11/0.40  % (28750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.40  % (28750)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.40  
% 0.11/0.40  % (28750)Memory used [KB]: 10618
% 0.11/0.40  % (28750)Time elapsed: 0.103 s
% 0.11/0.40  % (28750)------------------------------
% 0.11/0.40  % (28750)------------------------------
% 0.11/0.49  % (28807)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 0.11/0.50  % (28851)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 0.11/0.51  % (28824)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 0.11/0.52  % (28830)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 0.11/0.52  % (28836)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 0.11/0.53  % (28840)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 0.11/0.53  % (28847)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 0.11/0.54  % (28843)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 0.11/0.54  % (28849)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.72/0.65  % (28824)Refutation not found, incomplete strategy% (28824)------------------------------
% 2.72/0.65  % (28824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.72/0.65  % (28824)Termination reason: Refutation not found, incomplete strategy
% 2.72/0.65  
% 2.72/0.65  % (28824)Memory used [KB]: 6140
% 2.72/0.65  % (28824)Time elapsed: 0.239 s
% 2.72/0.65  % (28824)------------------------------
% 2.72/0.65  % (28824)------------------------------
% 3.36/0.71  % (28738)Time limit reached!
% 3.36/0.71  % (28738)------------------------------
% 3.36/0.71  % (28738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.71  % (28738)Termination reason: Time limit
% 3.36/0.71  
% 3.36/0.71  % (28738)Memory used [KB]: 8571
% 3.36/0.71  % (28738)Time elapsed: 0.417 s
% 3.36/0.71  % (28738)------------------------------
% 3.36/0.71  % (28738)------------------------------
% 3.91/0.80  % (28935)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 3.91/0.81  % (28745)Time limit reached!
% 3.91/0.81  % (28745)------------------------------
% 3.91/0.81  % (28745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.91/0.81  % (28745)Termination reason: Time limit
% 3.91/0.81  
% 3.91/0.81  % (28745)Memory used [KB]: 9594
% 3.91/0.81  % (28745)Time elapsed: 0.516 s
% 3.91/0.81  % (28745)------------------------------
% 3.91/0.81  % (28745)------------------------------
% 3.91/0.81  % (28734)Time limit reached!
% 3.91/0.81  % (28734)------------------------------
% 3.91/0.81  % (28734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.91/0.81  % (28734)Termination reason: Time limit
% 3.91/0.81  
% 3.91/0.81  % (28734)Memory used [KB]: 8571
% 3.91/0.81  % (28734)Time elapsed: 0.518 s
% 3.91/0.81  % (28734)------------------------------
% 3.91/0.81  % (28734)------------------------------
% 3.91/0.81  % (28950)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 3.91/0.84  % (28836)Time limit reached!
% 3.91/0.84  % (28836)------------------------------
% 3.91/0.84  % (28836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.91/0.84  % (28836)Termination reason: Time limit
% 3.91/0.84  % (28836)Termination phase: Saturation
% 3.91/0.84  
% 3.91/0.84  % (28836)Memory used [KB]: 8827
% 3.91/0.84  % (28836)Time elapsed: 0.400 s
% 3.91/0.84  % (28836)------------------------------
% 3.91/0.84  % (28836)------------------------------
% 3.91/0.86  % (28840)Time limit reached!
% 3.91/0.86  % (28840)------------------------------
% 3.91/0.86  % (28840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.91/0.86  % (28840)Termination reason: Time limit
% 3.91/0.86  
% 3.91/0.86  % (28840)Memory used [KB]: 14328
% 3.91/0.86  % (28840)Time elapsed: 0.409 s
% 3.91/0.86  % (28840)------------------------------
% 3.91/0.86  % (28840)------------------------------
% 4.74/0.90  % (28749)Time limit reached!
% 4.74/0.90  % (28749)------------------------------
% 4.74/0.90  % (28749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.74/0.90  % (28749)Termination reason: Time limit
% 4.74/0.90  
% 4.74/0.90  % (28749)Memory used [KB]: 16502
% 4.74/0.90  % (28749)Time elapsed: 0.606 s
% 4.74/0.90  % (28749)------------------------------
% 4.74/0.90  % (28749)------------------------------
% 4.95/0.92  % (28761)Time limit reached!
% 4.95/0.92  % (28761)------------------------------
% 4.95/0.92  % (28761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.95/0.93  % (28963)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 4.95/0.93  % (28761)Termination reason: Time limit
% 4.95/0.93  
% 4.95/0.93  % (28761)Memory used [KB]: 8443
% 4.95/0.93  % (28761)Time elapsed: 0.629 s
% 4.95/0.93  % (28761)------------------------------
% 4.95/0.93  % (28761)------------------------------
% 4.95/0.93  % (28962)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 4.95/0.93  % (28964)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 4.95/0.94  % (28740)Time limit reached!
% 4.95/0.94  % (28740)------------------------------
% 4.95/0.94  % (28740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.95/0.94  % (28740)Termination reason: Time limit
% 4.95/0.94  
% 4.95/0.94  % (28740)Memory used [KB]: 11641
% 4.95/0.94  % (28740)Time elapsed: 0.623 s
% 4.95/0.94  % (28740)------------------------------
% 4.95/0.94  % (28740)------------------------------
% 4.95/0.95  % (28964)Refutation not found, incomplete strategy% (28964)------------------------------
% 4.95/0.95  % (28964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.95/0.96  % (28964)Termination reason: Refutation not found, incomplete strategy
% 4.95/0.96  
% 4.95/0.96  % (28964)Memory used [KB]: 1663
% 4.95/0.96  % (28964)Time elapsed: 0.069 s
% 4.95/0.96  % (28964)------------------------------
% 4.95/0.96  % (28964)------------------------------
% 4.95/0.98  % (28965)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 5.42/1.03  % (28967)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 5.42/1.03  % (28966)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 5.42/1.08  % (28968)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 5.42/1.08  % (28969)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 7.47/1.31  % (28962)Refutation found. Thanks to Tanya!
% 7.47/1.31  % SZS status Theorem for theBenchmark
% 8.19/1.33  % SZS output start Proof for theBenchmark
% 8.19/1.33  fof(f2915,plain,(
% 8.19/1.33    $false),
% 8.19/1.33    inference(unit_resulting_resolution,[],[f24,f23,f23,f2897,f70])).
% 8.19/1.33  fof(f70,plain,(
% 8.19/1.33    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 8.19/1.33    inference(equality_resolution,[],[f60])).
% 8.19/1.33  fof(f60,plain,(
% 8.19/1.33    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 8.19/1.33    inference(definition_unfolding,[],[f36,f29])).
% 8.19/1.33  fof(f29,plain,(
% 8.19/1.33    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 8.19/1.33    inference(cnf_transformation,[],[f6])).
% 8.19/1.33  fof(f6,axiom,(
% 8.19/1.33    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 8.19/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 8.19/1.33  fof(f36,plain,(
% 8.19/1.33    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 8.19/1.33    inference(cnf_transformation,[],[f22])).
% 8.19/1.33  fof(f22,plain,(
% 8.19/1.33    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 8.19/1.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).
% 8.19/1.33  fof(f21,plain,(
% 8.19/1.33    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 8.19/1.33    introduced(choice_axiom,[])).
% 8.19/1.33  fof(f20,plain,(
% 8.19/1.33    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 8.19/1.33    inference(rectify,[],[f19])).
% 8.19/1.33  fof(f19,plain,(
% 8.19/1.33    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 8.19/1.33    inference(flattening,[],[f18])).
% 8.19/1.33  fof(f18,plain,(
% 8.19/1.33    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 8.19/1.33    inference(nnf_transformation,[],[f10])).
% 8.19/1.33  fof(f10,plain,(
% 8.19/1.33    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 8.19/1.33    inference(ennf_transformation,[],[f3])).
% 8.19/1.33  fof(f3,axiom,(
% 8.19/1.33    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 8.19/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 8.19/1.33  fof(f2897,plain,(
% 8.19/1.33    r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK2))),
% 8.19/1.33    inference(subsumption_resolution,[],[f2896,f23])).
% 8.19/1.33  fof(f2896,plain,(
% 8.19/1.33    r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) | sK0 = sK1),
% 8.19/1.33    inference(duplicate_literal_removal,[],[f2888])).
% 8.19/1.33  fof(f2888,plain,(
% 8.19/1.33    r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) | sK0 = sK1 | sK0 = sK1 | sK0 = sK1),
% 8.19/1.33    inference(resolution,[],[f2880,f70])).
% 8.19/1.33  fof(f2880,plain,(
% 8.19/1.33    r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK2))),
% 8.19/1.33    inference(subsumption_resolution,[],[f2879,f24])).
% 8.19/1.33  fof(f2879,plain,(
% 8.19/1.33    r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) | r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 = sK2),
% 8.19/1.33    inference(duplicate_literal_removal,[],[f2871])).
% 8.19/1.33  fof(f2871,plain,(
% 8.19/1.33    r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) | r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 = sK2 | sK0 = sK2 | sK0 = sK2),
% 8.19/1.33    inference(resolution,[],[f2811,f70])).
% 8.19/1.33  fof(f2811,plain,(
% 8.19/1.33    r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) | r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 8.19/1.33    inference(subsumption_resolution,[],[f2761,f65])).
% 8.19/1.33  fof(f65,plain,(
% 8.19/1.33    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 8.19/1.33    inference(equality_resolution,[],[f64])).
% 8.19/1.33  fof(f64,plain,(
% 8.19/1.33    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 8.19/1.33    inference(equality_resolution,[],[f57])).
% 8.19/1.33  fof(f57,plain,(
% 8.19/1.33    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 8.19/1.33    inference(definition_unfolding,[],[f39,f29])).
% 8.19/1.33  fof(f39,plain,(
% 8.19/1.33    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 8.19/1.33    inference(cnf_transformation,[],[f22])).
% 8.19/1.33  fof(f2761,plain,(
% 8.19/1.33    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) | r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 8.19/1.33    inference(superposition,[],[f166,f2714])).
% 8.19/1.33  fof(f2714,plain,(
% 8.19/1.33    sK0 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) | r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 8.19/1.33    inference(subsumption_resolution,[],[f2713,f67])).
% 8.19/1.33  fof(f67,plain,(
% 8.19/1.33    ( ! [X2,X0,X5] : (r2_hidden(X5,k2_enumset1(X0,X0,X5,X2))) )),
% 8.19/1.33    inference(equality_resolution,[],[f66])).
% 8.19/1.33  fof(f66,plain,(
% 8.19/1.33    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X5,X2) != X3) )),
% 8.19/1.33    inference(equality_resolution,[],[f58])).
% 8.19/1.33  fof(f58,plain,(
% 8.19/1.33    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 8.19/1.33    inference(definition_unfolding,[],[f38,f29])).
% 8.19/1.33  fof(f38,plain,(
% 8.19/1.33    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 8.19/1.33    inference(cnf_transformation,[],[f22])).
% 8.19/1.33  fof(f2713,plain,(
% 8.19/1.33    ~r2_hidden(sK1,k2_enumset1(sK0,sK0,sK1,sK2)) | r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))),
% 8.19/1.33    inference(subsumption_resolution,[],[f2665,f67])).
% 8.19/1.33  fof(f2665,plain,(
% 8.19/1.33    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK2)) | ~r2_hidden(sK1,k2_enumset1(sK0,sK0,sK1,sK2)) | r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))),
% 8.19/1.33    inference(superposition,[],[f186,f2615])).
% 8.19/1.33  fof(f2615,plain,(
% 8.19/1.33    sK1 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) | r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))),
% 8.19/1.33    inference(subsumption_resolution,[],[f2614,f65])).
% 8.19/1.33  fof(f2614,plain,(
% 8.19/1.33    ~r2_hidden(sK2,k2_enumset1(sK0,sK0,sK1,sK2)) | r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | sK1 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) | sK0 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))),
% 8.19/1.33    inference(subsumption_resolution,[],[f2566,f65])).
% 8.19/1.33  fof(f2566,plain,(
% 8.19/1.33    ~r2_hidden(sK2,k2_enumset1(sK1,sK1,sK1,sK2)) | ~r2_hidden(sK2,k2_enumset1(sK0,sK0,sK1,sK2)) | r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | sK1 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) | sK0 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))),
% 8.19/1.33    inference(superposition,[],[f186,f1286])).
% 8.19/1.33  fof(f1286,plain,(
% 8.19/1.33    sK2 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) | sK1 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) | sK0 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))),
% 8.19/1.33    inference(duplicate_literal_removal,[],[f1269])).
% 8.19/1.33  fof(f1269,plain,(
% 8.19/1.33    sK2 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) | sK1 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) | sK2 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) | sK1 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) | sK0 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))),
% 8.19/1.33    inference(resolution,[],[f339,f70])).
% 8.19/1.33  fof(f339,plain,(
% 8.19/1.33    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK0,sK0,sK1,sK2)) | sK2 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) | sK1 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))),
% 8.19/1.33    inference(duplicate_literal_removal,[],[f322])).
% 8.19/1.33  fof(f322,plain,(
% 8.19/1.33    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK0,sK0,sK1,sK2)) | sK2 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) | sK1 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) | sK1 = sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))),
% 8.19/1.33    inference(resolution,[],[f157,f70])).
% 8.19/1.33  fof(f157,plain,(
% 8.19/1.33    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK1,sK1,sK1,sK2)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK0,sK0,sK1,sK2))),
% 8.19/1.33    inference(equality_resolution,[],[f79])).
% 8.19/1.33  fof(f79,plain,(
% 8.19/1.33    ( ! [X0] : (k2_enumset1(sK1,sK1,sK1,sK2) != X0 | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),X0),k2_enumset1(sK0,sK0,sK1,sK2)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),X0),X0)) )),
% 8.19/1.33    inference(superposition,[],[f46,f49])).
% 8.19/1.33  fof(f49,plain,(
% 8.19/1.33    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 8.19/1.33    inference(definition_unfolding,[],[f33,f28])).
% 8.19/1.33  fof(f28,plain,(
% 8.19/1.33    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.19/1.33    inference(cnf_transformation,[],[f2])).
% 8.19/1.33  fof(f2,axiom,(
% 8.19/1.33    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 8.19/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 8.19/1.33  fof(f33,plain,(
% 8.19/1.33    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 8.19/1.33    inference(cnf_transformation,[],[f17])).
% 8.19/1.33  fof(f17,plain,(
% 8.19/1.33    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 8.19/1.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).
% 8.19/1.33  fof(f16,plain,(
% 8.19/1.33    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 8.19/1.33    introduced(choice_axiom,[])).
% 8.19/1.33  fof(f15,plain,(
% 8.19/1.33    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 8.19/1.33    inference(rectify,[],[f14])).
% 8.19/1.33  fof(f14,plain,(
% 8.19/1.33    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 8.19/1.33    inference(flattening,[],[f13])).
% 8.19/1.33  fof(f13,plain,(
% 8.19/1.33    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 8.19/1.33    inference(nnf_transformation,[],[f1])).
% 8.19/1.33  fof(f1,axiom,(
% 8.19/1.33    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 8.19/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 8.19/1.33  fof(f46,plain,(
% 8.19/1.33    k5_xboole_0(k2_enumset1(sK0,sK0,sK1,sK2),k3_xboole_0(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0))) != k2_enumset1(sK1,sK1,sK1,sK2)),
% 8.19/1.33    inference(definition_unfolding,[],[f25,f28,f29,f45,f44])).
% 8.19/1.33  fof(f44,plain,(
% 8.19/1.33    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 8.19/1.33    inference(definition_unfolding,[],[f27,f29])).
% 8.19/1.33  fof(f27,plain,(
% 8.19/1.33    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 8.19/1.33    inference(cnf_transformation,[],[f5])).
% 8.19/1.33  fof(f5,axiom,(
% 8.19/1.33    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 8.19/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 8.19/1.33  fof(f45,plain,(
% 8.19/1.33    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 8.19/1.33    inference(definition_unfolding,[],[f26,f44])).
% 8.19/1.33  fof(f26,plain,(
% 8.19/1.33    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 8.19/1.33    inference(cnf_transformation,[],[f4])).
% 8.19/1.33  fof(f4,axiom,(
% 8.19/1.33    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 8.19/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 8.19/1.33  fof(f25,plain,(
% 8.19/1.33    k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2)),
% 8.19/1.33    inference(cnf_transformation,[],[f12])).
% 8.19/1.33  fof(f12,plain,(
% 8.19/1.33    k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2) & sK0 != sK2 & sK0 != sK1),
% 8.19/1.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f11])).
% 8.19/1.33  fof(f11,plain,(
% 8.19/1.33    ? [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1) => (k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2) & sK0 != sK2 & sK0 != sK1)),
% 8.19/1.33    introduced(choice_axiom,[])).
% 8.19/1.33  fof(f9,plain,(
% 8.19/1.33    ? [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 8.19/1.33    inference(ennf_transformation,[],[f8])).
% 8.19/1.33  fof(f8,negated_conjecture,(
% 8.19/1.33    ~! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 8.19/1.33    inference(negated_conjecture,[],[f7])).
% 8.19/1.33  fof(f7,conjecture,(
% 8.19/1.33    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 8.19/1.33    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_enumset1)).
% 8.19/1.33  fof(f186,plain,(
% 8.19/1.33    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK1,sK1,sK1,sK2)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK0,sK0,sK1,sK2)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 8.19/1.33    inference(equality_resolution,[],[f81])).
% 8.19/1.33  fof(f81,plain,(
% 8.19/1.33    ( ! [X2] : (k2_enumset1(sK1,sK1,sK1,sK2) != X2 | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),X2),k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),X2),k2_enumset1(sK0,sK0,sK1,sK2)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),X2),X2)) )),
% 8.19/1.33    inference(superposition,[],[f46,f47])).
% 8.19/1.33  fof(f47,plain,(
% 8.19/1.33    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 8.19/1.33    inference(definition_unfolding,[],[f35,f28])).
% 8.19/1.33  fof(f35,plain,(
% 8.19/1.33    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 8.19/1.33    inference(cnf_transformation,[],[f17])).
% 8.19/1.33  fof(f166,plain,(
% 8.19/1.33    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK1,sK1,sK1,sK2))),
% 8.19/1.33    inference(equality_resolution,[],[f80])).
% 8.19/1.33  fof(f80,plain,(
% 8.19/1.33    ( ! [X1] : (k2_enumset1(sK1,sK1,sK1,sK2) != X1 | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),X1),k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK1,sK2),k2_enumset1(sK0,sK0,sK0,sK0),X1),X1)) )),
% 8.19/1.33    inference(superposition,[],[f46,f48])).
% 8.19/1.33  fof(f48,plain,(
% 8.19/1.33    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 8.19/1.33    inference(definition_unfolding,[],[f34,f28])).
% 8.19/1.33  fof(f34,plain,(
% 8.19/1.33    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 8.19/1.33    inference(cnf_transformation,[],[f17])).
% 8.19/1.33  fof(f23,plain,(
% 8.19/1.33    sK0 != sK1),
% 8.19/1.33    inference(cnf_transformation,[],[f12])).
% 8.19/1.33  fof(f24,plain,(
% 8.19/1.33    sK0 != sK2),
% 8.19/1.33    inference(cnf_transformation,[],[f12])).
% 8.19/1.33  % SZS output end Proof for theBenchmark
% 8.19/1.33  % (28962)------------------------------
% 8.19/1.33  % (28962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.19/1.33  % (28962)Termination reason: Refutation
% 8.19/1.33  
% 8.19/1.33  % (28962)Memory used [KB]: 3454
% 8.19/1.33  % (28962)Time elapsed: 0.463 s
% 8.19/1.33  % (28962)------------------------------
% 8.19/1.33  % (28962)------------------------------
% 8.19/1.33  % (28730)Success in time 1.057 s
%------------------------------------------------------------------------------
