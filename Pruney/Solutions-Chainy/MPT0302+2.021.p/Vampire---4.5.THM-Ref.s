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
% DateTime   : Thu Dec  3 12:42:01 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 261 expanded)
%              Number of leaves         :   16 (  72 expanded)
%              Depth                    :   21
%              Number of atoms          :  274 (1013 expanded)
%              Number of equality atoms :   77 ( 368 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f186,plain,(
    $false ),
    inference(subsumption_resolution,[],[f182,f41])).

fof(f41,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK0 != sK1
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) )
   => ( sK0 != sK1
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(f182,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f177,f75])).

fof(f75,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f74,f48])).

fof(f48,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f62,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f19,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f177,plain,(
    ! [X0] :
      ( r2_hidden(sK8(sK0,X0),X0)
      | sK0 = X0 ) ),
    inference(resolution,[],[f176,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_hidden(sK8(X0,X1),X1) ) ),
    inference(resolution,[],[f57,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(sK8(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK8(X0,X1),X0)
        & r2_hidden(sK8(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f20,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK8(X0,X1),X0)
        & r2_hidden(sK8(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f176,plain,(
    ! [X0] : r1_tarski(sK0,X0) ),
    inference(subsumption_resolution,[],[f175,f154])).

fof(f154,plain,(
    r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f150,f42])).

fof(f42,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f150,plain,
    ( r1_tarski(sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f147,f107])).

fof(f107,plain,(
    ! [X0] :
      ( r2_hidden(sK8(k1_xboole_0,X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f82,f77])).

fof(f77,plain,(
    ! [X3] : r1_tarski(k1_xboole_0,X3) ),
    inference(resolution,[],[f65,f75])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f21,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f147,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_tarski(sK0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,(
    ! [X0] :
      ( r1_tarski(sK0,sK1)
      | ~ r2_hidden(X0,sK1)
      | r1_tarski(sK0,sK1) ) ),
    inference(resolution,[],[f137,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f137,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK9(sK0,X11),sK1)
      | r1_tarski(sK0,X11)
      | ~ r2_hidden(X10,sK1) ) ),
    inference(resolution,[],[f123,f85])).

fof(f85,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X6,sK1) ) ),
    inference(superposition,[],[f58,f40])).

fof(f40,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f32])).

% (22881)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f123,plain,(
    ! [X24,X23,X25,X22] :
      ( r2_hidden(k4_tarski(sK9(X24,X25),X22),k2_zfmisc_1(X24,X23))
      | ~ r2_hidden(X22,X23)
      | r1_tarski(X24,X25) ) ),
    inference(resolution,[],[f70,f65])).

fof(f70,plain,(
    ! [X0,X10,X1,X9] :
      ( ~ r2_hidden(X9,X0)
      | ~ r2_hidden(X10,X1)
      | r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK2(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2))
              & r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
                & r2_hidden(sK6(X0,X1,X8),X1)
                & r2_hidden(sK5(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f27,f30,f29,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK2(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK2(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK2(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
        & r2_hidden(sK6(X0,X1,X8),X1)
        & r2_hidden(sK5(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f175,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | ~ r1_tarski(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f174,f43])).

fof(f43,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f174,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | sK0 = sK1
      | ~ r1_tarski(sK0,sK1) ) ),
    inference(resolution,[],[f173,f57])).

fof(f173,plain,(
    ! [X0] :
      ( ~ r2_xboole_0(sK0,sK1)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f143,f156])).

fof(f156,plain,(
    r2_hidden(sK8(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f155,f43])).

fof(f155,plain,
    ( sK0 = sK1
    | r2_hidden(sK8(sK0,sK1),sK1) ),
    inference(resolution,[],[f154,f82])).

fof(f143,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK8(sK0,X5),sK1)
      | r1_tarski(sK0,X4)
      | ~ r2_xboole_0(sK0,X5) ) ),
    inference(resolution,[],[f136,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f136,plain,(
    ! [X8,X9] :
      ( r2_hidden(X8,sK0)
      | r1_tarski(sK0,X9)
      | ~ r2_hidden(X8,sK1) ) ),
    inference(resolution,[],[f123,f88])).

fof(f88,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X7,sK0) ) ),
    inference(superposition,[],[f59,f40])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:37:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (800325634)
% 0.21/0.38  ipcrm: permission denied for id (800391172)
% 0.21/0.38  ipcrm: permission denied for id (800456710)
% 0.21/0.39  ipcrm: permission denied for id (800587786)
% 0.21/0.39  ipcrm: permission denied for id (800686095)
% 0.21/0.39  ipcrm: permission denied for id (800718864)
% 0.21/0.40  ipcrm: permission denied for id (800751633)
% 0.21/0.40  ipcrm: permission denied for id (800817172)
% 0.21/0.40  ipcrm: permission denied for id (800882711)
% 0.21/0.41  ipcrm: permission denied for id (800915480)
% 0.21/0.41  ipcrm: permission denied for id (800948249)
% 0.21/0.42  ipcrm: permission denied for id (801144865)
% 0.21/0.42  ipcrm: permission denied for id (801210403)
% 0.21/0.42  ipcrm: permission denied for id (801407018)
% 0.21/0.43  ipcrm: permission denied for id (801505325)
% 0.21/0.43  ipcrm: permission denied for id (801538094)
% 0.21/0.43  ipcrm: permission denied for id (801603635)
% 0.21/0.43  ipcrm: permission denied for id (801636404)
% 0.21/0.43  ipcrm: permission denied for id (801669173)
% 0.21/0.43  ipcrm: permission denied for id (801701943)
% 0.21/0.44  ipcrm: permission denied for id (801767484)
% 0.21/0.44  ipcrm: permission denied for id (801833022)
% 0.21/0.44  ipcrm: permission denied for id (801898560)
% 0.21/0.44  ipcrm: permission denied for id (801964098)
% 0.21/0.45  ipcrm: permission denied for id (801996867)
% 0.21/0.45  ipcrm: permission denied for id (802062405)
% 0.21/0.45  ipcrm: permission denied for id (802095176)
% 0.21/0.45  ipcrm: permission denied for id (802291791)
% 0.21/0.46  ipcrm: permission denied for id (802324560)
% 0.21/0.46  ipcrm: permission denied for id (802390098)
% 0.21/0.46  ipcrm: permission denied for id (802488405)
% 0.21/0.46  ipcrm: permission denied for id (802586714)
% 0.21/0.47  ipcrm: permission denied for id (802652252)
% 0.21/0.47  ipcrm: permission denied for id (802685021)
% 0.21/0.47  ipcrm: permission denied for id (802783326)
% 0.21/0.48  ipcrm: permission denied for id (802947173)
% 0.21/0.48  ipcrm: permission denied for id (802979942)
% 0.21/0.48  ipcrm: permission denied for id (803012711)
% 0.21/0.48  ipcrm: permission denied for id (803045480)
% 0.21/0.49  ipcrm: permission denied for id (803209325)
% 0.21/0.49  ipcrm: permission denied for id (803307632)
% 0.21/0.49  ipcrm: permission denied for id (803340401)
% 0.21/0.49  ipcrm: permission denied for id (803438708)
% 0.21/0.50  ipcrm: permission denied for id (803504246)
% 0.21/0.50  ipcrm: permission denied for id (803569785)
% 0.21/0.51  ipcrm: permission denied for id (803733631)
% 1.16/0.66  % (22855)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.16/0.66  % (22854)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.16/0.66  % (22858)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.16/0.66  % (22856)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.16/0.66  % (22864)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.16/0.66  % (22863)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.16/0.67  % (22853)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.16/0.67  % (22866)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.43/0.67  % (22871)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.43/0.67  % (22872)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.43/0.68  % (22867)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.43/0.68  % (22865)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.43/0.68  % (22855)Refutation found. Thanks to Tanya!
% 1.43/0.68  % SZS status Theorem for theBenchmark
% 1.43/0.68  % SZS output start Proof for theBenchmark
% 1.43/0.68  fof(f186,plain,(
% 1.43/0.68    $false),
% 1.43/0.68    inference(subsumption_resolution,[],[f182,f41])).
% 1.43/0.68  fof(f41,plain,(
% 1.43/0.68    k1_xboole_0 != sK0),
% 1.43/0.68    inference(cnf_transformation,[],[f23])).
% 1.43/0.68  fof(f23,plain,(
% 1.43/0.68    sK0 != sK1 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 1.43/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f22])).
% 1.43/0.68  fof(f22,plain,(
% 1.43/0.68    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)) => (sK0 != sK1 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0))),
% 1.43/0.68    introduced(choice_axiom,[])).
% 1.43/0.68  fof(f16,plain,(
% 1.43/0.68    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 1.43/0.68    inference(flattening,[],[f15])).
% 1.43/0.68  fof(f15,plain,(
% 1.43/0.68    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 1.43/0.68    inference(ennf_transformation,[],[f11])).
% 1.43/0.68  fof(f11,negated_conjecture,(
% 1.43/0.68    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.43/0.68    inference(negated_conjecture,[],[f10])).
% 1.43/0.68  fof(f10,conjecture,(
% 1.43/0.68    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.43/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).
% 1.43/0.68  fof(f182,plain,(
% 1.43/0.68    k1_xboole_0 = sK0),
% 1.43/0.68    inference(resolution,[],[f177,f75])).
% 1.43/0.68  fof(f75,plain,(
% 1.43/0.68    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.43/0.68    inference(subsumption_resolution,[],[f74,f48])).
% 1.43/0.68  fof(f48,plain,(
% 1.43/0.68    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.43/0.68    inference(cnf_transformation,[],[f6])).
% 1.43/0.68  fof(f6,axiom,(
% 1.43/0.68    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.43/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.43/0.68  fof(f74,plain,(
% 1.43/0.68    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 1.43/0.68    inference(superposition,[],[f62,f47])).
% 1.43/0.68  fof(f47,plain,(
% 1.43/0.68    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.43/0.68    inference(cnf_transformation,[],[f5])).
% 1.43/0.68  fof(f5,axiom,(
% 1.43/0.68    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.43/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.43/0.68  fof(f62,plain,(
% 1.43/0.68    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.43/0.68    inference(cnf_transformation,[],[f35])).
% 1.43/0.68  fof(f35,plain,(
% 1.43/0.68    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.43/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f19,f34])).
% 1.43/0.68  fof(f34,plain,(
% 1.43/0.68    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)))),
% 1.43/0.68    introduced(choice_axiom,[])).
% 1.43/0.68  fof(f19,plain,(
% 1.43/0.68    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.43/0.68    inference(ennf_transformation,[],[f12])).
% 1.43/0.68  fof(f12,plain,(
% 1.43/0.68    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.43/0.68    inference(rectify,[],[f3])).
% 1.43/0.68  fof(f3,axiom,(
% 1.43/0.68    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.43/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.43/0.68  fof(f177,plain,(
% 1.43/0.68    ( ! [X0] : (r2_hidden(sK8(sK0,X0),X0) | sK0 = X0) )),
% 1.43/0.68    inference(resolution,[],[f176,f82])).
% 1.43/0.68  fof(f82,plain,(
% 1.43/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_hidden(sK8(X0,X1),X1)) )),
% 1.43/0.68    inference(resolution,[],[f57,f63])).
% 1.43/0.68  fof(f63,plain,(
% 1.43/0.68    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_hidden(sK8(X0,X1),X1)) )),
% 1.43/0.68    inference(cnf_transformation,[],[f37])).
% 1.43/0.68  fof(f37,plain,(
% 1.43/0.68    ! [X0,X1] : ((~r2_hidden(sK8(X0,X1),X0) & r2_hidden(sK8(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 1.43/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f20,f36])).
% 1.43/0.68  fof(f36,plain,(
% 1.43/0.68    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK8(X0,X1),X0) & r2_hidden(sK8(X0,X1),X1)))),
% 1.43/0.68    introduced(choice_axiom,[])).
% 1.43/0.68  fof(f20,plain,(
% 1.43/0.68    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 1.43/0.68    inference(ennf_transformation,[],[f4])).
% 1.43/0.68  fof(f4,axiom,(
% 1.43/0.68    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 1.43/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).
% 1.43/0.68  fof(f57,plain,(
% 1.43/0.68    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.43/0.68    inference(cnf_transformation,[],[f18])).
% 1.43/0.68  fof(f18,plain,(
% 1.43/0.68    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 1.43/0.68    inference(flattening,[],[f17])).
% 1.43/0.68  fof(f17,plain,(
% 1.43/0.68    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 1.43/0.68    inference(ennf_transformation,[],[f13])).
% 1.43/0.68  fof(f13,plain,(
% 1.43/0.68    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 1.43/0.68    inference(unused_predicate_definition_removal,[],[f2])).
% 1.43/0.68  fof(f2,axiom,(
% 1.43/0.68    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.43/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.43/0.68  fof(f176,plain,(
% 1.43/0.68    ( ! [X0] : (r1_tarski(sK0,X0)) )),
% 1.43/0.68    inference(subsumption_resolution,[],[f175,f154])).
% 1.43/0.68  fof(f154,plain,(
% 1.43/0.68    r1_tarski(sK0,sK1)),
% 1.43/0.68    inference(subsumption_resolution,[],[f150,f42])).
% 1.43/0.68  fof(f42,plain,(
% 1.43/0.68    k1_xboole_0 != sK1),
% 1.43/0.68    inference(cnf_transformation,[],[f23])).
% 1.43/0.68  fof(f150,plain,(
% 1.43/0.68    r1_tarski(sK0,sK1) | k1_xboole_0 = sK1),
% 1.43/0.68    inference(resolution,[],[f147,f107])).
% 1.43/0.68  fof(f107,plain,(
% 1.43/0.68    ( ! [X0] : (r2_hidden(sK8(k1_xboole_0,X0),X0) | k1_xboole_0 = X0) )),
% 1.43/0.68    inference(resolution,[],[f82,f77])).
% 1.43/0.68  fof(f77,plain,(
% 1.43/0.68    ( ! [X3] : (r1_tarski(k1_xboole_0,X3)) )),
% 1.43/0.68    inference(resolution,[],[f65,f75])).
% 1.43/0.68  fof(f65,plain,(
% 1.43/0.68    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.43/0.68    inference(cnf_transformation,[],[f39])).
% 1.43/0.68  fof(f39,plain,(
% 1.43/0.68    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 1.43/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f21,f38])).
% 1.43/0.68  fof(f38,plain,(
% 1.43/0.68    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 1.43/0.68    introduced(choice_axiom,[])).
% 1.43/0.68  fof(f21,plain,(
% 1.43/0.68    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.43/0.68    inference(ennf_transformation,[],[f14])).
% 1.43/0.68  fof(f14,plain,(
% 1.43/0.68    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.43/0.68    inference(unused_predicate_definition_removal,[],[f1])).
% 1.43/0.68  fof(f1,axiom,(
% 1.43/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.43/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.43/0.68  fof(f147,plain,(
% 1.43/0.68    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(sK0,sK1)) )),
% 1.43/0.68    inference(duplicate_literal_removal,[],[f145])).
% 1.43/0.68  fof(f145,plain,(
% 1.43/0.68    ( ! [X0] : (r1_tarski(sK0,sK1) | ~r2_hidden(X0,sK1) | r1_tarski(sK0,sK1)) )),
% 1.43/0.68    inference(resolution,[],[f137,f66])).
% 1.43/0.68  fof(f66,plain,(
% 1.43/0.68    ( ! [X0,X1] : (~r2_hidden(sK9(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.43/0.68    inference(cnf_transformation,[],[f39])).
% 1.43/0.68  fof(f137,plain,(
% 1.43/0.68    ( ! [X10,X11] : (r2_hidden(sK9(sK0,X11),sK1) | r1_tarski(sK0,X11) | ~r2_hidden(X10,sK1)) )),
% 1.43/0.68    inference(resolution,[],[f123,f85])).
% 1.43/0.68  fof(f85,plain,(
% 1.43/0.68    ( ! [X6,X7] : (~r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X6,sK1)) )),
% 1.43/0.68    inference(superposition,[],[f58,f40])).
% 1.43/0.68  fof(f40,plain,(
% 1.43/0.68    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 1.43/0.68    inference(cnf_transformation,[],[f23])).
% 1.43/0.68  fof(f58,plain,(
% 1.43/0.68    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.43/0.68    inference(cnf_transformation,[],[f33])).
% 1.43/0.68  fof(f33,plain,(
% 1.43/0.68    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.43/0.68    inference(flattening,[],[f32])).
% 1.43/0.68  % (22881)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.43/0.68  fof(f32,plain,(
% 1.43/0.68    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.43/0.68    inference(nnf_transformation,[],[f8])).
% 1.43/0.68  fof(f8,axiom,(
% 1.43/0.68    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.43/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.43/0.68  fof(f123,plain,(
% 1.43/0.68    ( ! [X24,X23,X25,X22] : (r2_hidden(k4_tarski(sK9(X24,X25),X22),k2_zfmisc_1(X24,X23)) | ~r2_hidden(X22,X23) | r1_tarski(X24,X25)) )),
% 1.43/0.68    inference(resolution,[],[f70,f65])).
% 1.43/0.68  fof(f70,plain,(
% 1.43/0.68    ( ! [X0,X10,X1,X9] : (~r2_hidden(X9,X0) | ~r2_hidden(X10,X1) | r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))) )),
% 1.43/0.68    inference(equality_resolution,[],[f69])).
% 1.43/0.68  fof(f69,plain,(
% 1.43/0.68    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.43/0.68    inference(equality_resolution,[],[f52])).
% 1.43/0.68  fof(f52,plain,(
% 1.43/0.68    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.43/0.68    inference(cnf_transformation,[],[f31])).
% 1.43/0.68  fof(f31,plain,(
% 1.43/0.68    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.43/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f27,f30,f29,f28])).
% 1.43/0.68  fof(f28,plain,(
% 1.43/0.68    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.43/0.68    introduced(choice_axiom,[])).
% 1.43/0.68  fof(f29,plain,(
% 1.43/0.68    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK2(X0,X1,X2) = k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)))),
% 1.43/0.68    introduced(choice_axiom,[])).
% 1.43/0.68  fof(f30,plain,(
% 1.43/0.68    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)))),
% 1.43/0.68    introduced(choice_axiom,[])).
% 1.43/0.68  fof(f27,plain,(
% 1.43/0.68    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.43/0.68    inference(rectify,[],[f26])).
% 1.43/0.68  fof(f26,plain,(
% 1.43/0.68    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.43/0.68    inference(nnf_transformation,[],[f7])).
% 1.43/0.68  fof(f7,axiom,(
% 1.43/0.68    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.43/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.43/0.68  fof(f175,plain,(
% 1.43/0.68    ( ! [X0] : (r1_tarski(sK0,X0) | ~r1_tarski(sK0,sK1)) )),
% 1.43/0.68    inference(subsumption_resolution,[],[f174,f43])).
% 1.43/0.68  fof(f43,plain,(
% 1.43/0.68    sK0 != sK1),
% 1.43/0.68    inference(cnf_transformation,[],[f23])).
% 1.43/0.68  fof(f174,plain,(
% 1.43/0.68    ( ! [X0] : (r1_tarski(sK0,X0) | sK0 = sK1 | ~r1_tarski(sK0,sK1)) )),
% 1.43/0.68    inference(resolution,[],[f173,f57])).
% 1.43/0.68  fof(f173,plain,(
% 1.43/0.68    ( ! [X0] : (~r2_xboole_0(sK0,sK1) | r1_tarski(sK0,X0)) )),
% 1.43/0.68    inference(resolution,[],[f143,f156])).
% 1.43/0.68  fof(f156,plain,(
% 1.43/0.68    r2_hidden(sK8(sK0,sK1),sK1)),
% 1.43/0.68    inference(subsumption_resolution,[],[f155,f43])).
% 1.43/0.68  fof(f155,plain,(
% 1.43/0.68    sK0 = sK1 | r2_hidden(sK8(sK0,sK1),sK1)),
% 1.43/0.68    inference(resolution,[],[f154,f82])).
% 1.43/0.68  fof(f143,plain,(
% 1.43/0.68    ( ! [X4,X5] : (~r2_hidden(sK8(sK0,X5),sK1) | r1_tarski(sK0,X4) | ~r2_xboole_0(sK0,X5)) )),
% 1.43/0.68    inference(resolution,[],[f136,f64])).
% 1.43/0.68  fof(f64,plain,(
% 1.43/0.68    ( ! [X0,X1] : (~r2_hidden(sK8(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 1.43/0.68    inference(cnf_transformation,[],[f37])).
% 1.43/0.68  fof(f136,plain,(
% 1.43/0.68    ( ! [X8,X9] : (r2_hidden(X8,sK0) | r1_tarski(sK0,X9) | ~r2_hidden(X8,sK1)) )),
% 1.43/0.68    inference(resolution,[],[f123,f88])).
% 1.43/0.68  fof(f88,plain,(
% 1.43/0.68    ( ! [X6,X7] : (~r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X7,sK0)) )),
% 1.43/0.68    inference(superposition,[],[f59,f40])).
% 1.43/0.68  fof(f59,plain,(
% 1.43/0.68    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.43/0.68    inference(cnf_transformation,[],[f33])).
% 1.43/0.68  % SZS output end Proof for theBenchmark
% 1.43/0.68  % (22855)------------------------------
% 1.43/0.68  % (22855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.68  % (22855)Termination reason: Refutation
% 1.43/0.68  
% 1.43/0.68  % (22855)Memory used [KB]: 6396
% 1.43/0.68  % (22855)Time elapsed: 0.121 s
% 1.43/0.68  % (22855)------------------------------
% 1.43/0.68  % (22855)------------------------------
% 1.43/0.68  % (22852)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.43/0.68  % (22715)Success in time 0.319 s
%------------------------------------------------------------------------------
