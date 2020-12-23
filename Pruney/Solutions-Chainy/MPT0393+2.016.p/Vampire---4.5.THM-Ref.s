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
% DateTime   : Thu Dec  3 12:45:53 EST 2020

% Result     : Theorem 2.00s
% Output     : Refutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 502 expanded)
%              Number of leaves         :   13 ( 153 expanded)
%              Depth                    :   28
%              Number of atoms          :  299 (3118 expanded)
%              Number of equality atoms :  115 (1378 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f859,plain,(
    $false ),
    inference(resolution,[],[f847,f784])).

fof(f784,plain,(
    r2_hidden(sK6(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f778,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK6(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK6(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f18,f37])).

fof(f37,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK6(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK6(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f778,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(superposition,[],[f90,f748])).

fof(f748,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f747,f736])).

fof(f736,plain,
    ( ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f733,f46])).

fof(f46,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f19])).

fof(f19,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f733,plain,
    ( ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(duplicate_literal_removal,[],[f732])).

fof(f732,plain,
    ( ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(superposition,[],[f54,f727])).

fof(f727,plain,
    ( sK0 = sK2(k1_tarski(sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f726,f704])).

fof(f704,plain,
    ( ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK2(k1_tarski(sK0),sK0) ),
    inference(resolution,[],[f516,f91])).

fof(f91,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f516,plain,
    ( r2_hidden(sK2(k1_tarski(sK0),sK0),k1_tarski(sK0))
    | ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2] :
      ( sK0 != X2
      | r2_hidden(sK2(k1_tarski(sK0),X2),k1_tarski(sK0))
      | ~ r2_hidden(sK1(k1_tarski(sK0),X2),X2)
      | k1_xboole_0 = k1_tarski(sK0) ) ),
    inference(superposition,[],[f46,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | ~ r2_hidden(sK1(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
                  & r2_hidden(sK2(X0,X1),X0) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK1(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK3(X0,X5))
                    & r2_hidden(sK3(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f25,f24,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK1(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK1(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(sK1(X0,X1),X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK3(X0,X5))
        & r2_hidden(sK3(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f726,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK2(k1_tarski(sK0),sK0)
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    inference(subsumption_resolution,[],[f725,f90])).

fof(f725,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK2(k1_tarski(sK0),sK0)
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    inference(subsumption_resolution,[],[f724,f46])).

fof(f724,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK2(k1_tarski(sK0),sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f716])).

fof(f716,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK2(k1_tarski(sK0),sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(resolution,[],[f704,f52])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK1(X0,X1),X4)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(sK1(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | ~ r2_hidden(sK1(X0,X1),sK2(X0,X1))
      | ~ r2_hidden(sK1(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f747,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    inference(subsumption_resolution,[],[f746,f90])).

fof(f746,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    inference(subsumption_resolution,[],[f745,f46])).

fof(f745,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f737])).

fof(f737,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = k1_setfam_1(k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(resolution,[],[f736,f52])).

fof(f90,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f847,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f838,f98])).

fof(f98,plain,(
    ! [X3,X1] :
      ( ~ r2_hidden(X3,sK6(X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(condensation,[],[f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK6(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f838,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK6(k1_xboole_0))
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f826,f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f826,plain,(
    r1_tarski(k1_xboole_0,sK6(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f814,f81])).

fof(f81,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_setfam_1(X0)
      | k1_xboole_0 != X0 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | k1_xboole_0 != X1
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f814,plain,(
    r1_tarski(k1_setfam_1(k1_xboole_0),sK6(k1_xboole_0)) ),
    inference(resolution,[],[f784,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 09:45:37 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.49  % (8380)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.51  % (8388)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.51  % (8381)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.52  % (8396)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.23/0.52  % (8389)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.23/0.53  % (8381)Refutation not found, incomplete strategy% (8381)------------------------------
% 0.23/0.53  % (8381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (8377)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.53  % (8381)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (8381)Memory used [KB]: 10618
% 0.23/0.53  % (8381)Time elapsed: 0.095 s
% 0.23/0.53  % (8381)------------------------------
% 0.23/0.53  % (8381)------------------------------
% 0.23/0.53  % (8376)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.53  % (8375)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.53  % (8379)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.53  % (8398)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.23/0.53  % (8385)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.53  % (8384)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.23/0.53  % (8386)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.23/0.53  % (8375)Refutation not found, incomplete strategy% (8375)------------------------------
% 0.23/0.53  % (8375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (8387)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.54  % (8373)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.54  % (8375)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (8375)Memory used [KB]: 10746
% 0.23/0.54  % (8375)Time elapsed: 0.111 s
% 0.23/0.54  % (8375)------------------------------
% 0.23/0.54  % (8375)------------------------------
% 0.23/0.54  % (8373)Refutation not found, incomplete strategy% (8373)------------------------------
% 0.23/0.54  % (8373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (8373)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (8373)Memory used [KB]: 1663
% 0.23/0.54  % (8373)Time elapsed: 0.088 s
% 0.23/0.54  % (8373)------------------------------
% 0.23/0.54  % (8373)------------------------------
% 0.23/0.54  % (8392)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.23/0.54  % (8393)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.23/0.54  % (8374)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.54  % (8394)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.23/0.54  % (8402)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.23/0.54  % (8391)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.23/0.54  % (8383)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.23/0.54  % (8400)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.23/0.55  % (8401)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.23/0.55  % (8399)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.23/0.55  % (8397)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.55  % (8395)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.55  % (8383)Refutation not found, incomplete strategy% (8383)------------------------------
% 0.23/0.55  % (8383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (8383)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (8383)Memory used [KB]: 10618
% 0.23/0.55  % (8383)Time elapsed: 0.119 s
% 0.23/0.55  % (8383)------------------------------
% 0.23/0.55  % (8383)------------------------------
% 0.23/0.55  % (8390)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.23/0.55  % (8378)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.56  % (8393)Refutation not found, incomplete strategy% (8393)------------------------------
% 0.23/0.56  % (8393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (8393)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (8393)Memory used [KB]: 10746
% 0.23/0.56  % (8393)Time elapsed: 0.131 s
% 0.23/0.56  % (8393)------------------------------
% 0.23/0.56  % (8393)------------------------------
% 0.23/0.56  % (8384)Refutation not found, incomplete strategy% (8384)------------------------------
% 0.23/0.56  % (8384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (8384)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (8384)Memory used [KB]: 10746
% 0.23/0.56  % (8384)Time elapsed: 0.134 s
% 0.23/0.56  % (8384)------------------------------
% 0.23/0.56  % (8384)------------------------------
% 0.23/0.56  % (8382)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.43/0.56  % (8394)Refutation not found, incomplete strategy% (8394)------------------------------
% 1.43/0.56  % (8394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (8394)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (8394)Memory used [KB]: 1663
% 1.43/0.56  % (8394)Time elapsed: 0.141 s
% 1.43/0.56  % (8394)------------------------------
% 1.43/0.56  % (8394)------------------------------
% 2.00/0.65  % (8431)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.00/0.66  % (8419)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.00/0.66  % (8396)Refutation found. Thanks to Tanya!
% 2.00/0.66  % SZS status Theorem for theBenchmark
% 2.00/0.66  % SZS output start Proof for theBenchmark
% 2.00/0.66  fof(f859,plain,(
% 2.00/0.66    $false),
% 2.00/0.66    inference(resolution,[],[f847,f784])).
% 2.00/0.66  fof(f784,plain,(
% 2.00/0.66    r2_hidden(sK6(k1_xboole_0),k1_xboole_0)),
% 2.00/0.66    inference(resolution,[],[f778,f68])).
% 2.00/0.66  fof(f68,plain,(
% 2.00/0.66    ( ! [X0,X1] : (r2_hidden(sK6(X1),X1) | ~r2_hidden(X0,X1)) )),
% 2.00/0.66    inference(cnf_transformation,[],[f38])).
% 2.00/0.66  fof(f38,plain,(
% 2.00/0.66    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK6(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK6(X1),X1)) | ~r2_hidden(X0,X1))),
% 2.00/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f18,f37])).
% 2.00/0.66  fof(f37,plain,(
% 2.00/0.66    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK6(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK6(X1),X1)))),
% 2.00/0.66    introduced(choice_axiom,[])).
% 2.00/0.66  fof(f18,plain,(
% 2.00/0.66    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 2.00/0.66    inference(ennf_transformation,[],[f9])).
% 2.00/0.66  fof(f9,axiom,(
% 2.00/0.66    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 2.00/0.66  fof(f778,plain,(
% 2.00/0.66    r2_hidden(sK0,k1_xboole_0)),
% 2.00/0.66    inference(superposition,[],[f90,f748])).
% 2.00/0.66  fof(f748,plain,(
% 2.00/0.66    k1_xboole_0 = k1_tarski(sK0)),
% 2.00/0.66    inference(subsumption_resolution,[],[f747,f736])).
% 2.00/0.66  fof(f736,plain,(
% 2.00/0.66    ~r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | k1_xboole_0 = k1_tarski(sK0)),
% 2.00/0.66    inference(subsumption_resolution,[],[f733,f46])).
% 2.00/0.66  fof(f46,plain,(
% 2.00/0.66    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 2.00/0.66    inference(cnf_transformation,[],[f20])).
% 2.00/0.66  fof(f20,plain,(
% 2.00/0.66    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 2.00/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f19])).
% 2.00/0.66  fof(f19,plain,(
% 2.00/0.66    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => sK0 != k1_setfam_1(k1_tarski(sK0))),
% 2.00/0.66    introduced(choice_axiom,[])).
% 2.00/0.66  fof(f14,plain,(
% 2.00/0.66    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 2.00/0.66    inference(ennf_transformation,[],[f13])).
% 2.00/0.66  fof(f13,negated_conjecture,(
% 2.00/0.66    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.00/0.66    inference(negated_conjecture,[],[f12])).
% 2.00/0.66  fof(f12,conjecture,(
% 2.00/0.66    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 2.00/0.66  fof(f733,plain,(
% 2.00/0.66    ~r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | sK0 = k1_setfam_1(k1_tarski(sK0)) | k1_xboole_0 = k1_tarski(sK0)),
% 2.00/0.66    inference(duplicate_literal_removal,[],[f732])).
% 2.00/0.66  fof(f732,plain,(
% 2.00/0.66    ~r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | sK0 = k1_setfam_1(k1_tarski(sK0)) | ~r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | k1_xboole_0 = k1_tarski(sK0) | k1_xboole_0 = k1_tarski(sK0)),
% 2.00/0.66    inference(superposition,[],[f54,f727])).
% 2.00/0.66  fof(f727,plain,(
% 2.00/0.66    sK0 = sK2(k1_tarski(sK0),sK0) | k1_xboole_0 = k1_tarski(sK0)),
% 2.00/0.66    inference(subsumption_resolution,[],[f726,f704])).
% 2.00/0.66  fof(f704,plain,(
% 2.00/0.66    ~r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | k1_xboole_0 = k1_tarski(sK0) | sK0 = sK2(k1_tarski(sK0),sK0)),
% 2.00/0.66    inference(resolution,[],[f516,f91])).
% 2.00/0.66  fof(f91,plain,(
% 2.00/0.66    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 2.00/0.66    inference(equality_resolution,[],[f64])).
% 2.00/0.66  fof(f64,plain,(
% 2.00/0.66    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.00/0.66    inference(cnf_transformation,[],[f36])).
% 2.00/0.66  fof(f36,plain,(
% 2.00/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.00/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).
% 2.00/0.66  fof(f35,plain,(
% 2.00/0.66    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 2.00/0.66    introduced(choice_axiom,[])).
% 2.00/0.66  fof(f34,plain,(
% 2.00/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.00/0.66    inference(rectify,[],[f33])).
% 2.00/0.66  fof(f33,plain,(
% 2.00/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.00/0.66    inference(nnf_transformation,[],[f3])).
% 2.00/0.66  fof(f3,axiom,(
% 2.00/0.66    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 2.00/0.66  fof(f516,plain,(
% 2.00/0.66    r2_hidden(sK2(k1_tarski(sK0),sK0),k1_tarski(sK0)) | ~r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | k1_xboole_0 = k1_tarski(sK0)),
% 2.00/0.66    inference(equality_resolution,[],[f102])).
% 2.00/0.66  fof(f102,plain,(
% 2.00/0.66    ( ! [X2] : (sK0 != X2 | r2_hidden(sK2(k1_tarski(sK0),X2),k1_tarski(sK0)) | ~r2_hidden(sK1(k1_tarski(sK0),X2),X2) | k1_xboole_0 = k1_tarski(sK0)) )),
% 2.00/0.66    inference(superposition,[],[f46,f53])).
% 2.00/0.66  fof(f53,plain,(
% 2.00/0.66    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1) | k1_xboole_0 = X0) )),
% 2.00/0.66    inference(cnf_transformation,[],[f26])).
% 2.00/0.66  fof(f26,plain,(
% 2.00/0.66    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)) | ~r2_hidden(sK1(X0,X1),X1)) & (! [X4] : (r2_hidden(sK1(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK3(X0,X5)) & r2_hidden(sK3(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 2.00/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f25,f24,f23])).
% 2.00/0.66  fof(f23,plain,(
% 2.00/0.66    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK1(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK1(X0,X1),X1)) & (! [X4] : (r2_hidden(sK1(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK1(X0,X1),X1))))),
% 2.00/0.66    introduced(choice_axiom,[])).
% 2.00/0.66  fof(f24,plain,(
% 2.00/0.66    ! [X1,X0] : (? [X3] : (~r2_hidden(sK1(X0,X1),X3) & r2_hidden(X3,X0)) => (~r2_hidden(sK1(X0,X1),sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 2.00/0.66    introduced(choice_axiom,[])).
% 2.00/0.66  fof(f25,plain,(
% 2.00/0.66    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK3(X0,X5)) & r2_hidden(sK3(X0,X5),X0)))),
% 2.00/0.66    introduced(choice_axiom,[])).
% 2.00/0.66  fof(f22,plain,(
% 2.00/0.66    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 2.00/0.66    inference(rectify,[],[f21])).
% 2.00/0.66  fof(f21,plain,(
% 2.00/0.66    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 2.00/0.66    inference(nnf_transformation,[],[f15])).
% 2.00/0.66  fof(f15,plain,(
% 2.00/0.66    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 2.00/0.66    inference(ennf_transformation,[],[f10])).
% 2.00/0.66  fof(f10,axiom,(
% 2.00/0.66    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).
% 2.00/0.66  fof(f726,plain,(
% 2.00/0.66    k1_xboole_0 = k1_tarski(sK0) | sK0 = sK2(k1_tarski(sK0),sK0) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)),
% 2.00/0.66    inference(subsumption_resolution,[],[f725,f90])).
% 2.00/0.66  fof(f725,plain,(
% 2.00/0.66    k1_xboole_0 = k1_tarski(sK0) | sK0 = sK2(k1_tarski(sK0),sK0) | ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)),
% 2.00/0.66    inference(subsumption_resolution,[],[f724,f46])).
% 2.00/0.66  fof(f724,plain,(
% 2.00/0.66    k1_xboole_0 = k1_tarski(sK0) | sK0 = sK2(k1_tarski(sK0),sK0) | sK0 = k1_setfam_1(k1_tarski(sK0)) | ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)),
% 2.00/0.66    inference(duplicate_literal_removal,[],[f716])).
% 2.00/0.66  fof(f716,plain,(
% 2.00/0.66    k1_xboole_0 = k1_tarski(sK0) | sK0 = sK2(k1_tarski(sK0),sK0) | sK0 = k1_setfam_1(k1_tarski(sK0)) | ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | k1_xboole_0 = k1_tarski(sK0)),
% 2.00/0.66    inference(resolution,[],[f704,f52])).
% 2.00/0.66  fof(f52,plain,(
% 2.00/0.66    ( ! [X4,X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK1(X0,X1),X4) | ~r2_hidden(X4,X0) | r2_hidden(sK1(X0,X1),X1) | k1_xboole_0 = X0) )),
% 2.00/0.66    inference(cnf_transformation,[],[f26])).
% 2.00/0.66  fof(f54,plain,(
% 2.00/0.66    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | ~r2_hidden(sK1(X0,X1),sK2(X0,X1)) | ~r2_hidden(sK1(X0,X1),X1) | k1_xboole_0 = X0) )),
% 2.00/0.66    inference(cnf_transformation,[],[f26])).
% 2.00/0.66  fof(f747,plain,(
% 2.00/0.66    k1_xboole_0 = k1_tarski(sK0) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)),
% 2.00/0.66    inference(subsumption_resolution,[],[f746,f90])).
% 2.00/0.66  fof(f746,plain,(
% 2.00/0.66    k1_xboole_0 = k1_tarski(sK0) | ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)),
% 2.00/0.66    inference(subsumption_resolution,[],[f745,f46])).
% 2.00/0.66  fof(f745,plain,(
% 2.00/0.66    k1_xboole_0 = k1_tarski(sK0) | sK0 = k1_setfam_1(k1_tarski(sK0)) | ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)),
% 2.00/0.66    inference(duplicate_literal_removal,[],[f737])).
% 2.00/0.66  fof(f737,plain,(
% 2.00/0.66    k1_xboole_0 = k1_tarski(sK0) | sK0 = k1_setfam_1(k1_tarski(sK0)) | ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) | k1_xboole_0 = k1_tarski(sK0)),
% 2.00/0.66    inference(resolution,[],[f736,f52])).
% 2.00/0.66  fof(f90,plain,(
% 2.00/0.66    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 2.00/0.66    inference(equality_resolution,[],[f89])).
% 2.00/0.66  fof(f89,plain,(
% 2.00/0.66    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 2.00/0.66    inference(equality_resolution,[],[f65])).
% 2.00/0.66  fof(f65,plain,(
% 2.00/0.66    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.00/0.66    inference(cnf_transformation,[],[f36])).
% 2.00/0.66  fof(f847,plain,(
% 2.00/0.66    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.00/0.66    inference(subsumption_resolution,[],[f838,f98])).
% 2.00/0.66  fof(f98,plain,(
% 2.00/0.66    ( ! [X3,X1] : (~r2_hidden(X3,sK6(X1)) | ~r2_hidden(X3,X1)) )),
% 2.00/0.66    inference(condensation,[],[f69])).
% 2.00/0.66  fof(f69,plain,(
% 2.00/0.66    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK6(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 2.00/0.66    inference(cnf_transformation,[],[f38])).
% 2.00/0.66  fof(f838,plain,(
% 2.00/0.66    ( ! [X0] : (r2_hidden(X0,sK6(k1_xboole_0)) | ~r2_hidden(X0,k1_xboole_0)) )),
% 2.00/0.66    inference(resolution,[],[f826,f61])).
% 2.00/0.66  fof(f61,plain,(
% 2.00/0.66    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.00/0.66    inference(cnf_transformation,[],[f32])).
% 2.00/0.66  fof(f32,plain,(
% 2.00/0.66    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.00/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 2.00/0.66  fof(f31,plain,(
% 2.00/0.66    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.00/0.66    introduced(choice_axiom,[])).
% 2.00/0.66  fof(f30,plain,(
% 2.00/0.66    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.00/0.66    inference(rectify,[],[f29])).
% 2.00/0.66  fof(f29,plain,(
% 2.00/0.66    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.00/0.66    inference(nnf_transformation,[],[f17])).
% 2.00/0.66  fof(f17,plain,(
% 2.00/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.00/0.66    inference(ennf_transformation,[],[f1])).
% 2.00/0.66  fof(f1,axiom,(
% 2.00/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.00/0.66  fof(f826,plain,(
% 2.00/0.66    r1_tarski(k1_xboole_0,sK6(k1_xboole_0))),
% 2.00/0.66    inference(forward_demodulation,[],[f814,f81])).
% 2.00/0.66  fof(f81,plain,(
% 2.00/0.66    k1_xboole_0 = k1_setfam_1(k1_xboole_0)),
% 2.00/0.66    inference(equality_resolution,[],[f80])).
% 2.00/0.66  fof(f80,plain,(
% 2.00/0.66    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(X0) | k1_xboole_0 != X0) )),
% 2.00/0.66    inference(equality_resolution,[],[f56])).
% 2.00/0.66  fof(f56,plain,(
% 2.00/0.66    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | k1_xboole_0 != X1 | k1_xboole_0 != X0) )),
% 2.00/0.66    inference(cnf_transformation,[],[f26])).
% 2.00/0.66  fof(f814,plain,(
% 2.00/0.66    r1_tarski(k1_setfam_1(k1_xboole_0),sK6(k1_xboole_0))),
% 2.00/0.66    inference(resolution,[],[f784,f57])).
% 2.00/0.66  fof(f57,plain,(
% 2.00/0.66    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 2.00/0.66    inference(cnf_transformation,[],[f16])).
% 2.00/0.66  fof(f16,plain,(
% 2.00/0.66    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 2.00/0.66    inference(ennf_transformation,[],[f11])).
% 2.00/0.66  fof(f11,axiom,(
% 2.00/0.66    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 2.00/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).
% 2.00/0.66  % SZS output end Proof for theBenchmark
% 2.00/0.66  % (8396)------------------------------
% 2.00/0.66  % (8396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.66  % (8396)Termination reason: Refutation
% 2.00/0.66  
% 2.00/0.66  % (8396)Memory used [KB]: 2302
% 2.00/0.66  % (8396)Time elapsed: 0.216 s
% 2.00/0.66  % (8396)------------------------------
% 2.00/0.66  % (8396)------------------------------
% 2.00/0.66  % (8372)Success in time 0.274 s
%------------------------------------------------------------------------------
