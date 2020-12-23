%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0929+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 114 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :   18
%              Number of atoms          :  151 ( 433 expanded)
%              Number of equality atoms :  150 ( 432 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(subsumption_resolution,[],[f150,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_tarski(X4,X5) != k4_tarski(X6,X7)
      | k2_mcart_1(k4_tarski(X4,X5)) = X5 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X5
      | k2_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X5
      | k4_tarski(X4,X5) != X0
      | k2_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_mcart_1(X0) = X1
            | ( sK7(X0,X1) != X1
              & k4_tarski(sK6(X0,X1),sK7(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X3
          & k4_tarski(X2,X3) = X0 )
     => ( sK7(X0,X1) != X1
        & k4_tarski(sK6(X0,X1),sK7(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_mcart_1(X0) = X1
            | ? [X2,X3] :
                ( X1 != X3
                & k4_tarski(X2,X3) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ( k2_mcart_1(X0) = X3
            | ? [X4,X5] :
                ( X3 != X5
                & k4_tarski(X4,X5) = X0 ) )
          & ( ! [X4,X5] :
                ( X3 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X3 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X5
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X5 ) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k2_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_mcart_1)).

fof(f150,plain,(
    sK4 != k2_mcart_1(k4_tarski(sK3,sK4)) ),
    inference(superposition,[],[f94,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_mcart_1(X1) = k20_mcart_1(k4_tarski(X0,X1)) ),
    inference(superposition,[],[f28,f51])).

fof(f28,plain,(
    ! [X0] : k20_mcart_1(X0) = k2_mcart_1(k2_mcart_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k20_mcart_1(X0) = k2_mcart_1(k2_mcart_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_mcart_1)).

fof(f94,plain,(
    sK4 != k20_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4))) ),
    inference(subsumption_resolution,[],[f93,f54])).

fof(f54,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_tarski(X4,X5) != k4_tarski(X6,X7)
      | k1_mcart_1(k4_tarski(X4,X5)) = X4 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X4
      | k1_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X4
      | k4_tarski(X4,X5) != X0
      | k1_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ( sK8(X0,X1) != X1
              & k4_tarski(sK8(X0,X1),sK9(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X2
          & k4_tarski(X2,X3) = X0 )
     => ( sK8(X0,X1) != X1
        & k4_tarski(sK8(X0,X1),sK9(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ? [X2,X3] :
                ( X1 != X2
                & k4_tarski(X2,X3) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ( k1_mcart_1(X0) = X3
            | ? [X4,X5] :
                ( X3 != X4
                & k4_tarski(X4,X5) = X0 ) )
          & ( ! [X4,X5] :
                ( X3 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X3 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X4
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X4 ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k1_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_mcart_1)).

fof(f93,plain,
    ( sK0 != k1_mcart_1(k4_tarski(sK0,sK1))
    | sK4 != k20_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4))) ),
    inference(backward_demodulation,[],[f92,f88])).

fof(f88,plain,(
    ! [X2,X3] : k17_mcart_1(k4_tarski(X2,X3)) = k1_mcart_1(X2) ),
    inference(superposition,[],[f25,f54])).

fof(f25,plain,(
    ! [X0] : k17_mcart_1(X0) = k1_mcart_1(k1_mcart_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k17_mcart_1(X0) = k1_mcart_1(k1_mcart_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_mcart_1)).

fof(f92,plain,
    ( sK4 != k20_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))
    | sK0 != k17_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f91,f51])).

fof(f91,plain,
    ( sK1 != k2_mcart_1(k4_tarski(sK0,sK1))
    | sK4 != k20_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))
    | sK0 != k17_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) ),
    inference(backward_demodulation,[],[f60,f87])).

fof(f87,plain,(
    ! [X0,X1] : k2_mcart_1(X0) = k18_mcart_1(k4_tarski(X0,X1)) ),
    inference(superposition,[],[f26,f54])).

fof(f26,plain,(
    ! [X0] : k18_mcart_1(X0) = k2_mcart_1(k1_mcart_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k18_mcart_1(X0) = k2_mcart_1(k1_mcart_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_mcart_1)).

fof(f60,plain,
    ( sK4 != k20_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))
    | sK1 != k18_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))
    | sK0 != k17_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f59,f54])).

fof(f59,plain,
    ( sK3 != k1_mcart_1(k4_tarski(sK3,sK4))
    | sK4 != k20_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))
    | sK1 != k18_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))
    | sK0 != k17_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) ),
    inference(backward_demodulation,[],[f24,f58])).

fof(f58,plain,(
    ! [X2,X3] : k19_mcart_1(k4_tarski(X2,X3)) = k1_mcart_1(X3) ),
    inference(superposition,[],[f27,f51])).

fof(f27,plain,(
    ! [X0] : k19_mcart_1(X0) = k1_mcart_1(k2_mcart_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k19_mcart_1(X0) = k1_mcart_1(k2_mcart_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_mcart_1)).

fof(f24,plain,
    ( sK4 != k20_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))
    | sK3 != k19_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))
    | sK1 != k18_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))
    | sK0 != k17_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( sK4 != k20_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))
    | sK3 != k19_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))
    | sK1 != k18_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))
    | sK0 != k17_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X4
        | k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X3
        | k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X1
        | k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X0 )
   => ( sK4 != k20_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))
      | sK3 != k19_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))
      | sK1 != k18_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))
      | sK0 != k17_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X4
      | k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X3
      | k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X1
      | k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X4
        & k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X3
        & k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X1
        & k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X4
      & k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X3
      & k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X1
      & k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_mcart_1)).

%------------------------------------------------------------------------------
