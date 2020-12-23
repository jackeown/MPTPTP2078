%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:28 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 270 expanded)
%              Number of leaves         :   10 (  90 expanded)
%              Depth                    :   23
%              Number of atoms          :  265 (1858 expanded)
%              Number of equality atoms :  119 ( 668 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f657,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f644])).

fof(f644,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f22,f433])).

fof(f433,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(subsumption_resolution,[],[f432,f48])).

fof(f48,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f44,f46])).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(superposition,[],[f24,f23])).

fof(f23,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f432,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(X0))
      | k3_tarski(k1_tarski(X0)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f429])).

fof(f429,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(X0))
      | k3_tarski(k1_tarski(X0)) = X0
      | k3_tarski(k1_tarski(X0)) = X0
      | ~ r2_hidden(X0,k1_tarski(X0)) ) ),
    inference(resolution,[],[f419,f377])).

fof(f377,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(k1_tarski(X0),X1),X0)
      | k3_tarski(k1_tarski(X0)) = X1
      | ~ r2_hidden(X1,k1_tarski(X0)) ) ),
    inference(subsumption_resolution,[],[f376,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_tarski(X1))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f76,f38])).

fof(f38,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f12,f15,f14,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK1(X0,X1),X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_tarski(k1_tarski(X0)))
      | r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k3_tarski(k1_tarski(X0)))
      | ~ r2_hidden(X1,k3_tarski(k1_tarski(X0))) ) ),
    inference(superposition,[],[f40,f59])).

fof(f59,plain,(
    ! [X2,X1] :
      ( sK3(k1_tarski(X1),X2) = X1
      | ~ r2_hidden(X2,k3_tarski(k1_tarski(X1))) ) ),
    inference(resolution,[],[f54,f39])).

fof(f39,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1
      | X0 = X1 ) ),
    inference(superposition,[],[f45,f46])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f376,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(k1_tarski(X0),X1),X0)
      | k3_tarski(k1_tarski(X0)) = X1
      | r2_hidden(sK1(k1_tarski(X0),X1),X1)
      | ~ r2_hidden(X1,k1_tarski(X0)) ) ),
    inference(duplicate_literal_removal,[],[f373])).

fof(f373,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(k1_tarski(X0),X1),X0)
      | k3_tarski(k1_tarski(X0)) = X1
      | r2_hidden(sK1(k1_tarski(X0),X1),X1)
      | k3_tarski(k1_tarski(X0)) = X1
      | ~ r2_hidden(X1,k1_tarski(X0)) ) ),
    inference(superposition,[],[f28,f371])).

fof(f371,plain,(
    ! [X0,X1] :
      ( sK2(k1_tarski(X0),X1) = X0
      | k3_tarski(k1_tarski(X0)) = X1
      | ~ r2_hidden(X1,k1_tarski(X0)) ) ),
    inference(duplicate_literal_removal,[],[f365])).

fof(f365,plain,(
    ! [X0,X1] :
      ( sK2(k1_tarski(X0),X1) = X0
      | sK2(k1_tarski(X0),X1) = X0
      | k3_tarski(k1_tarski(X0)) = X1
      | ~ r2_hidden(X1,k1_tarski(X0)) ) ),
    inference(superposition,[],[f184,f46])).

fof(f184,plain,(
    ! [X6,X4,X5] :
      ( sK2(k2_tarski(X4,X5),X6) = X5
      | sK2(k2_tarski(X4,X5),X6) = X4
      | k3_tarski(k2_tarski(X4,X5)) = X6
      | ~ r2_hidden(X6,k2_tarski(X4,X5)) ) ),
    inference(subsumption_resolution,[],[f181,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(k2_tarski(X0,X1),X2),X2)
      | k3_tarski(k2_tarski(X0,X1)) = X2
      | sK2(k2_tarski(X0,X1),X2) = X0
      | sK2(k2_tarski(X0,X1),X2) = X1 ) ),
    inference(resolution,[],[f29,f45])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k3_tarski(X0) = X1
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f181,plain,(
    ! [X6,X4,X5] :
      ( k3_tarski(k2_tarski(X4,X5)) = X6
      | sK2(k2_tarski(X4,X5),X6) = X4
      | sK2(k2_tarski(X4,X5),X6) = X5
      | ~ r2_hidden(X6,k2_tarski(X4,X5))
      | ~ r2_hidden(sK1(k2_tarski(X4,X5),X6),X6) ) ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,(
    ! [X6,X4,X5] :
      ( k3_tarski(k2_tarski(X4,X5)) = X6
      | sK2(k2_tarski(X4,X5),X6) = X4
      | sK2(k2_tarski(X4,X5),X6) = X5
      | ~ r2_hidden(X6,k2_tarski(X4,X5))
      | k3_tarski(k2_tarski(X4,X5)) = X6
      | ~ r2_hidden(sK1(k2_tarski(X4,X5),X6),X6) ) ),
    inference(resolution,[],[f60,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(sK1(X0,X1),X3)
      | ~ r2_hidden(X3,X0)
      | k3_tarski(X0) = X1
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),sK2(X0,X1))
      | k3_tarski(X0) = X1
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f419,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(sK1(k1_tarski(X7),X8),X8)
      | ~ r2_hidden(X8,k1_tarski(X7))
      | k3_tarski(k1_tarski(X7)) = X8 ) ),
    inference(subsumption_resolution,[],[f416,f48])).

fof(f416,plain,(
    ! [X8,X7] :
      ( k3_tarski(k1_tarski(X7)) = X8
      | ~ r2_hidden(X8,k1_tarski(X7))
      | ~ r2_hidden(X7,k1_tarski(X7))
      | ~ r2_hidden(sK1(k1_tarski(X7),X8),X8) ) ),
    inference(duplicate_literal_removal,[],[f401])).

fof(f401,plain,(
    ! [X8,X7] :
      ( k3_tarski(k1_tarski(X7)) = X8
      | ~ r2_hidden(X8,k1_tarski(X7))
      | ~ r2_hidden(X7,k1_tarski(X7))
      | k3_tarski(k1_tarski(X7)) = X8
      | ~ r2_hidden(sK1(k1_tarski(X7),X8),X8) ) ),
    inference(resolution,[],[f377,f30])).

fof(f22,plain,(
    sK0 != k3_tarski(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    sK0 != k3_tarski(k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).

fof(f9,plain,
    ( ? [X0] : k3_tarski(k1_tarski(X0)) != X0
   => sK0 != k3_tarski(k1_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : k3_tarski(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:31:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (8566)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.49  % (8575)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.49  % (8566)Refutation not found, incomplete strategy% (8566)------------------------------
% 0.22/0.49  % (8566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (8566)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (8566)Memory used [KB]: 10618
% 0.22/0.49  % (8566)Time elapsed: 0.070 s
% 0.22/0.49  % (8566)------------------------------
% 0.22/0.49  % (8566)------------------------------
% 0.22/0.54  % (8582)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (8564)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (8560)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (8558)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.56  % (8561)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.56  % (8583)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.56  % (8583)Refutation not found, incomplete strategy% (8583)------------------------------
% 0.22/0.56  % (8583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (8583)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (8583)Memory used [KB]: 6140
% 0.22/0.56  % (8583)Time elapsed: 0.150 s
% 0.22/0.56  % (8583)------------------------------
% 0.22/0.56  % (8583)------------------------------
% 0.22/0.56  % (8563)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.56  % (8582)Refutation not found, incomplete strategy% (8582)------------------------------
% 0.22/0.56  % (8582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (8582)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (8582)Memory used [KB]: 6140
% 0.22/0.56  % (8582)Time elapsed: 0.141 s
% 0.22/0.56  % (8582)------------------------------
% 0.22/0.56  % (8582)------------------------------
% 0.22/0.56  % (8580)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.56  % (8565)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.56  % (8580)Refutation not found, incomplete strategy% (8580)------------------------------
% 0.22/0.56  % (8580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (8580)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (8580)Memory used [KB]: 10618
% 0.22/0.56  % (8580)Time elapsed: 0.159 s
% 0.22/0.56  % (8580)------------------------------
% 0.22/0.56  % (8580)------------------------------
% 0.22/0.57  % (8578)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.57  % (8567)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.57  % (8567)Refutation not found, incomplete strategy% (8567)------------------------------
% 0.22/0.57  % (8567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (8567)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (8567)Memory used [KB]: 6140
% 0.22/0.57  % (8567)Time elapsed: 0.161 s
% 0.22/0.57  % (8567)------------------------------
% 0.22/0.57  % (8567)------------------------------
% 0.22/0.57  % (8573)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.57  % (8572)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.58  % (8571)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.58  % (8581)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.58  % (8562)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.58  % (8581)Refutation not found, incomplete strategy% (8581)------------------------------
% 0.22/0.58  % (8581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (8581)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (8581)Memory used [KB]: 6140
% 0.22/0.58  % (8581)Time elapsed: 0.171 s
% 0.22/0.58  % (8581)------------------------------
% 0.22/0.58  % (8581)------------------------------
% 0.22/0.58  % (8570)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.58  % (8570)Refutation not found, incomplete strategy% (8570)------------------------------
% 0.22/0.58  % (8570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (8570)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (8570)Memory used [KB]: 1663
% 0.22/0.58  % (8570)Time elapsed: 0.140 s
% 0.22/0.58  % (8570)------------------------------
% 0.22/0.58  % (8570)------------------------------
% 0.22/0.59  % (8573)Refutation not found, incomplete strategy% (8573)------------------------------
% 0.22/0.59  % (8573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (8573)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (8573)Memory used [KB]: 1663
% 0.22/0.59  % (8573)Time elapsed: 0.181 s
% 0.22/0.59  % (8573)------------------------------
% 0.22/0.59  % (8573)------------------------------
% 0.22/0.59  % (8559)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.59  % (8572)Refutation not found, incomplete strategy% (8572)------------------------------
% 0.22/0.59  % (8572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (8572)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (8572)Memory used [KB]: 10618
% 0.22/0.59  % (8572)Time elapsed: 0.191 s
% 0.22/0.59  % (8572)------------------------------
% 0.22/0.59  % (8572)------------------------------
% 0.22/0.59  % (8579)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.59  % (8556)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.59  % (8584)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.59  % (8557)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.60  % (8557)Refutation not found, incomplete strategy% (8557)------------------------------
% 0.22/0.60  % (8557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (8557)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (8557)Memory used [KB]: 1663
% 0.22/0.60  % (8557)Time elapsed: 0.171 s
% 0.22/0.60  % (8557)------------------------------
% 0.22/0.60  % (8557)------------------------------
% 0.22/0.60  % (8584)Refutation not found, incomplete strategy% (8584)------------------------------
% 0.22/0.60  % (8584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (8584)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (8584)Memory used [KB]: 10618
% 0.22/0.60  % (8584)Time elapsed: 0.156 s
% 0.22/0.60  % (8584)------------------------------
% 0.22/0.60  % (8584)------------------------------
% 0.22/0.60  % (8574)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.87/0.60  % (8574)Refutation not found, incomplete strategy% (8574)------------------------------
% 1.87/0.60  % (8574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.60  % (8574)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.60  
% 1.87/0.60  % (8574)Memory used [KB]: 1663
% 1.87/0.60  % (8574)Time elapsed: 0.173 s
% 1.87/0.60  % (8574)------------------------------
% 1.87/0.60  % (8574)------------------------------
% 1.87/0.61  % (8577)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.87/0.61  % (8576)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.87/0.61  % (8569)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.87/0.61  % (8568)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 2.03/0.63  % (8585)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 2.03/0.63  % (8585)Refutation not found, incomplete strategy% (8585)------------------------------
% 2.03/0.63  % (8585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.63  % (8585)Termination reason: Refutation not found, incomplete strategy
% 2.03/0.63  
% 2.03/0.63  % (8585)Memory used [KB]: 1663
% 2.03/0.63  % (8585)Time elapsed: 0.198 s
% 2.03/0.63  % (8585)------------------------------
% 2.03/0.63  % (8585)------------------------------
% 2.03/0.63  % (8565)Refutation found. Thanks to Tanya!
% 2.03/0.63  % SZS status Theorem for theBenchmark
% 2.03/0.63  % SZS output start Proof for theBenchmark
% 2.03/0.63  fof(f657,plain,(
% 2.03/0.63    $false),
% 2.03/0.63    inference(trivial_inequality_removal,[],[f644])).
% 2.03/0.63  fof(f644,plain,(
% 2.03/0.63    sK0 != sK0),
% 2.03/0.63    inference(superposition,[],[f22,f433])).
% 2.03/0.63  fof(f433,plain,(
% 2.03/0.63    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 2.03/0.63    inference(subsumption_resolution,[],[f432,f48])).
% 2.03/0.63  fof(f48,plain,(
% 2.03/0.63    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 2.03/0.63    inference(superposition,[],[f44,f46])).
% 2.03/0.63  fof(f46,plain,(
% 2.03/0.63    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.03/0.63    inference(superposition,[],[f24,f23])).
% 2.03/0.63  fof(f23,plain,(
% 2.03/0.63    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f4])).
% 2.03/0.63  fof(f4,axiom,(
% 2.03/0.63    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
% 2.03/0.63  fof(f24,plain,(
% 2.03/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f3])).
% 2.03/0.63  fof(f3,axiom,(
% 2.03/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.03/0.63  fof(f44,plain,(
% 2.03/0.63    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 2.03/0.63    inference(equality_resolution,[],[f43])).
% 2.03/0.63  fof(f43,plain,(
% 2.03/0.63    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 2.03/0.63    inference(equality_resolution,[],[f33])).
% 2.03/0.63  fof(f33,plain,(
% 2.03/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.03/0.63    inference(cnf_transformation,[],[f21])).
% 2.03/0.63  fof(f21,plain,(
% 2.03/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.03/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).
% 2.03/0.63  fof(f20,plain,(
% 2.03/0.63    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.03/0.63    introduced(choice_axiom,[])).
% 2.03/0.63  fof(f19,plain,(
% 2.03/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.03/0.63    inference(rectify,[],[f18])).
% 2.03/0.63  fof(f18,plain,(
% 2.03/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.03/0.63    inference(flattening,[],[f17])).
% 2.03/0.63  fof(f17,plain,(
% 2.03/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.03/0.63    inference(nnf_transformation,[],[f1])).
% 2.03/0.63  fof(f1,axiom,(
% 2.03/0.63    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 2.03/0.63  fof(f432,plain,(
% 2.03/0.63    ( ! [X0] : (~r2_hidden(X0,k1_tarski(X0)) | k3_tarski(k1_tarski(X0)) = X0) )),
% 2.03/0.63    inference(duplicate_literal_removal,[],[f429])).
% 2.03/0.63  fof(f429,plain,(
% 2.03/0.63    ( ! [X0] : (~r2_hidden(X0,k1_tarski(X0)) | k3_tarski(k1_tarski(X0)) = X0 | k3_tarski(k1_tarski(X0)) = X0 | ~r2_hidden(X0,k1_tarski(X0))) )),
% 2.03/0.63    inference(resolution,[],[f419,f377])).
% 2.03/0.63  fof(f377,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r2_hidden(sK1(k1_tarski(X0),X1),X0) | k3_tarski(k1_tarski(X0)) = X1 | ~r2_hidden(X1,k1_tarski(X0))) )),
% 2.03/0.63    inference(subsumption_resolution,[],[f376,f78])).
% 2.03/0.63  fof(f78,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_tarski(X1)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 2.03/0.63    inference(resolution,[],[f76,f38])).
% 2.03/0.63  fof(f38,plain,(
% 2.03/0.63    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 2.03/0.63    inference(equality_resolution,[],[f27])).
% 2.03/0.63  fof(f27,plain,(
% 2.03/0.63    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 2.03/0.63    inference(cnf_transformation,[],[f16])).
% 2.03/0.63  fof(f16,plain,(
% 2.03/0.63    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 2.03/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f12,f15,f14,f13])).
% 2.03/0.63  fof(f13,plain,(
% 2.03/0.63    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 2.03/0.63    introduced(choice_axiom,[])).
% 2.03/0.63  fof(f14,plain,(
% 2.03/0.63    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))))),
% 2.03/0.63    introduced(choice_axiom,[])).
% 2.03/0.63  fof(f15,plain,(
% 2.03/0.63    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 2.03/0.63    introduced(choice_axiom,[])).
% 2.03/0.63  fof(f12,plain,(
% 2.03/0.63    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 2.03/0.63    inference(rectify,[],[f11])).
% 2.03/0.63  fof(f11,plain,(
% 2.03/0.63    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 2.03/0.63    inference(nnf_transformation,[],[f5])).
% 2.03/0.63  fof(f5,axiom,(
% 2.03/0.63    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 2.03/0.63  fof(f76,plain,(
% 2.03/0.63    ( ! [X0,X1] : (~r2_hidden(X1,k3_tarski(k1_tarski(X0))) | r2_hidden(X1,X0)) )),
% 2.03/0.63    inference(duplicate_literal_removal,[],[f73])).
% 2.03/0.63  fof(f73,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~r2_hidden(X1,k3_tarski(k1_tarski(X0))) | ~r2_hidden(X1,k3_tarski(k1_tarski(X0)))) )),
% 2.03/0.63    inference(superposition,[],[f40,f59])).
% 2.03/0.63  fof(f59,plain,(
% 2.03/0.63    ( ! [X2,X1] : (sK3(k1_tarski(X1),X2) = X1 | ~r2_hidden(X2,k3_tarski(k1_tarski(X1)))) )),
% 2.03/0.63    inference(resolution,[],[f54,f39])).
% 2.03/0.63  fof(f39,plain,(
% 2.03/0.63    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 2.03/0.63    inference(equality_resolution,[],[f26])).
% 2.03/0.63  fof(f26,plain,(
% 2.03/0.63    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 2.03/0.63    inference(cnf_transformation,[],[f16])).
% 2.03/0.63  fof(f54,plain,(
% 2.03/0.63    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | X0 = X1) )),
% 2.03/0.63    inference(duplicate_literal_removal,[],[f53])).
% 2.03/0.63  fof(f53,plain,(
% 2.03/0.63    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | X0 = X1 | X0 = X1) )),
% 2.03/0.63    inference(superposition,[],[f45,f46])).
% 2.03/0.63  fof(f45,plain,(
% 2.03/0.63    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 2.03/0.63    inference(equality_resolution,[],[f32])).
% 2.03/0.63  fof(f32,plain,(
% 2.03/0.63    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 2.03/0.63    inference(cnf_transformation,[],[f21])).
% 2.03/0.63  fof(f40,plain,(
% 2.03/0.63    ( ! [X0,X5] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 2.03/0.63    inference(equality_resolution,[],[f25])).
% 2.03/0.63  fof(f25,plain,(
% 2.03/0.63    ( ! [X0,X5,X1] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 2.03/0.63    inference(cnf_transformation,[],[f16])).
% 2.03/0.63  fof(f376,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r2_hidden(sK1(k1_tarski(X0),X1),X0) | k3_tarski(k1_tarski(X0)) = X1 | r2_hidden(sK1(k1_tarski(X0),X1),X1) | ~r2_hidden(X1,k1_tarski(X0))) )),
% 2.03/0.63    inference(duplicate_literal_removal,[],[f373])).
% 2.03/0.63  fof(f373,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r2_hidden(sK1(k1_tarski(X0),X1),X0) | k3_tarski(k1_tarski(X0)) = X1 | r2_hidden(sK1(k1_tarski(X0),X1),X1) | k3_tarski(k1_tarski(X0)) = X1 | ~r2_hidden(X1,k1_tarski(X0))) )),
% 2.03/0.63    inference(superposition,[],[f28,f371])).
% 2.03/0.63  fof(f371,plain,(
% 2.03/0.63    ( ! [X0,X1] : (sK2(k1_tarski(X0),X1) = X0 | k3_tarski(k1_tarski(X0)) = X1 | ~r2_hidden(X1,k1_tarski(X0))) )),
% 2.03/0.63    inference(duplicate_literal_removal,[],[f365])).
% 2.03/0.63  fof(f365,plain,(
% 2.03/0.63    ( ! [X0,X1] : (sK2(k1_tarski(X0),X1) = X0 | sK2(k1_tarski(X0),X1) = X0 | k3_tarski(k1_tarski(X0)) = X1 | ~r2_hidden(X1,k1_tarski(X0))) )),
% 2.03/0.63    inference(superposition,[],[f184,f46])).
% 2.03/0.63  fof(f184,plain,(
% 2.03/0.63    ( ! [X6,X4,X5] : (sK2(k2_tarski(X4,X5),X6) = X5 | sK2(k2_tarski(X4,X5),X6) = X4 | k3_tarski(k2_tarski(X4,X5)) = X6 | ~r2_hidden(X6,k2_tarski(X4,X5))) )),
% 2.03/0.63    inference(subsumption_resolution,[],[f181,f60])).
% 2.03/0.63  fof(f60,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (r2_hidden(sK1(k2_tarski(X0,X1),X2),X2) | k3_tarski(k2_tarski(X0,X1)) = X2 | sK2(k2_tarski(X0,X1),X2) = X0 | sK2(k2_tarski(X0,X1),X2) = X1) )),
% 2.03/0.63    inference(resolution,[],[f29,f45])).
% 2.03/0.63  fof(f29,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k3_tarski(X0) = X1 | r2_hidden(sK1(X0,X1),X1)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f16])).
% 2.03/0.63  fof(f181,plain,(
% 2.03/0.63    ( ! [X6,X4,X5] : (k3_tarski(k2_tarski(X4,X5)) = X6 | sK2(k2_tarski(X4,X5),X6) = X4 | sK2(k2_tarski(X4,X5),X6) = X5 | ~r2_hidden(X6,k2_tarski(X4,X5)) | ~r2_hidden(sK1(k2_tarski(X4,X5),X6),X6)) )),
% 2.03/0.63    inference(duplicate_literal_removal,[],[f170])).
% 2.03/0.63  fof(f170,plain,(
% 2.03/0.63    ( ! [X6,X4,X5] : (k3_tarski(k2_tarski(X4,X5)) = X6 | sK2(k2_tarski(X4,X5),X6) = X4 | sK2(k2_tarski(X4,X5),X6) = X5 | ~r2_hidden(X6,k2_tarski(X4,X5)) | k3_tarski(k2_tarski(X4,X5)) = X6 | ~r2_hidden(sK1(k2_tarski(X4,X5),X6),X6)) )),
% 2.03/0.63    inference(resolution,[],[f60,f30])).
% 2.03/0.63  fof(f30,plain,(
% 2.03/0.63    ( ! [X0,X3,X1] : (~r2_hidden(sK1(X0,X1),X3) | ~r2_hidden(X3,X0) | k3_tarski(X0) = X1 | ~r2_hidden(sK1(X0,X1),X1)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f16])).
% 2.03/0.63  fof(f28,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),sK2(X0,X1)) | k3_tarski(X0) = X1 | r2_hidden(sK1(X0,X1),X1)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f16])).
% 2.03/0.63  fof(f419,plain,(
% 2.03/0.63    ( ! [X8,X7] : (~r2_hidden(sK1(k1_tarski(X7),X8),X8) | ~r2_hidden(X8,k1_tarski(X7)) | k3_tarski(k1_tarski(X7)) = X8) )),
% 2.03/0.63    inference(subsumption_resolution,[],[f416,f48])).
% 2.03/0.63  fof(f416,plain,(
% 2.03/0.63    ( ! [X8,X7] : (k3_tarski(k1_tarski(X7)) = X8 | ~r2_hidden(X8,k1_tarski(X7)) | ~r2_hidden(X7,k1_tarski(X7)) | ~r2_hidden(sK1(k1_tarski(X7),X8),X8)) )),
% 2.03/0.63    inference(duplicate_literal_removal,[],[f401])).
% 2.03/0.63  fof(f401,plain,(
% 2.03/0.63    ( ! [X8,X7] : (k3_tarski(k1_tarski(X7)) = X8 | ~r2_hidden(X8,k1_tarski(X7)) | ~r2_hidden(X7,k1_tarski(X7)) | k3_tarski(k1_tarski(X7)) = X8 | ~r2_hidden(sK1(k1_tarski(X7),X8),X8)) )),
% 2.03/0.63    inference(resolution,[],[f377,f30])).
% 2.03/0.63  fof(f22,plain,(
% 2.03/0.63    sK0 != k3_tarski(k1_tarski(sK0))),
% 2.03/0.63    inference(cnf_transformation,[],[f10])).
% 2.03/0.63  fof(f10,plain,(
% 2.03/0.63    sK0 != k3_tarski(k1_tarski(sK0))),
% 2.03/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).
% 2.03/0.63  fof(f9,plain,(
% 2.03/0.63    ? [X0] : k3_tarski(k1_tarski(X0)) != X0 => sK0 != k3_tarski(k1_tarski(sK0))),
% 2.03/0.63    introduced(choice_axiom,[])).
% 2.03/0.63  fof(f8,plain,(
% 2.03/0.63    ? [X0] : k3_tarski(k1_tarski(X0)) != X0),
% 2.03/0.63    inference(ennf_transformation,[],[f7])).
% 2.03/0.63  fof(f7,negated_conjecture,(
% 2.03/0.63    ~! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 2.03/0.63    inference(negated_conjecture,[],[f6])).
% 2.03/0.63  fof(f6,conjecture,(
% 2.03/0.63    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 2.03/0.63  % SZS output end Proof for theBenchmark
% 2.03/0.63  % (8565)------------------------------
% 2.03/0.63  % (8565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.63  % (8565)Termination reason: Refutation
% 2.03/0.63  
% 2.03/0.63  % (8565)Memory used [KB]: 2174
% 2.03/0.63  % (8565)Time elapsed: 0.204 s
% 2.03/0.63  % (8565)------------------------------
% 2.03/0.63  % (8565)------------------------------
% 2.03/0.63  % (8555)Success in time 0.262 s
%------------------------------------------------------------------------------
