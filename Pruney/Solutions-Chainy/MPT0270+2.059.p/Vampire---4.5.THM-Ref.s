%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 857 expanded)
%              Number of leaves         :   10 ( 218 expanded)
%              Depth                    :   29
%              Number of atoms          :  338 (5910 expanded)
%              Number of equality atoms :  126 (1613 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1376,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1375,f69])).

fof(f69,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f68,f33])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f68,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f64,f34])).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(resolution,[],[f60,f59])).

fof(f59,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ( sK5(X0,X1,X2,X3) != X0
              & sK5(X0,X1,X2,X3) != X1
              & sK5(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( sK5(X0,X1,X2,X3) = X0
            | sK5(X0,X1,X2,X3) = X1
            | sK5(X0,X1,X2,X3) = X2
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).

fof(f28,plain,(
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
     => ( ( ( sK5(X0,X1,X2,X3) != X0
            & sK5(X0,X1,X2,X3) != X1
            & sK5(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( sK5(X0,X1,X2,X3) = X0
          | sK5(X0,X1,X2,X3) = X1
          | sK5(X0,X1,X2,X3) = X2
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
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
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP1(X2,X1,X0,X3)
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
        | ~ sP1(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP1(X2,X1,X0,X3)
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
        | ~ sP1(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X2,X1,X0,X3] :
      ( sP1(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f60,plain,(
    ! [X2,X0,X1] : sP1(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP1(X2,X1,X0,X3) )
      & ( sP1(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP1(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f11,f14])).

fof(f11,plain,(
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

fof(f1375,plain,(
    ~ r2_hidden(sK2,k1_tarski(sK2)) ),
    inference(resolution,[],[f1374,f1320])).

fof(f1320,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK3)
      | ~ r2_hidden(X3,k1_tarski(sK2)) ) ),
    inference(superposition,[],[f82,f1308])).

fof(f1308,plain,(
    sK3 = k4_xboole_0(sK3,k1_tarski(sK2)) ),
    inference(resolution,[],[f1307,f69])).

fof(f1307,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK2))
      | sK3 = k4_xboole_0(sK3,k1_tarski(sK2)) ) ),
    inference(condensation,[],[f1304])).

fof(f1304,plain,(
    ! [X2,X3] :
      ( sK3 = k4_xboole_0(sK3,k1_tarski(sK2))
      | ~ r2_hidden(X2,k1_tarski(sK2))
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f1302,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
              & r2_hidden(sK4(X0,X1,X2),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            & r2_hidden(sK4(X0,X1,X2),X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1302,plain,(
    ! [X1] :
      ( sP0(X1,X1,k1_tarski(sK2))
      | sK3 = k4_xboole_0(sK3,k1_tarski(sK2)) ) ),
    inference(subsumption_resolution,[],[f1301,f1219])).

fof(f1219,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,X3)
      | k4_xboole_0(X3,k1_tarski(X2)) = X3 ) ),
    inference(subsumption_resolution,[],[f1218,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f12])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1218,plain,(
    ! [X2,X3] :
      ( sP0(k1_tarski(X2),X3,X3)
      | r2_hidden(X2,X3)
      | k4_xboole_0(X3,k1_tarski(X2)) = X3 ) ),
    inference(subsumption_resolution,[],[f1208,f69])).

fof(f1208,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_tarski(X2))
      | sP0(k1_tarski(X2),X3,X3)
      | r2_hidden(X2,X3)
      | k4_xboole_0(X3,k1_tarski(X2)) = X3 ) ),
    inference(superposition,[],[f41,f1058])).

fof(f1058,plain,(
    ! [X10,X9] :
      ( sK4(k1_tarski(X9),X10,X10) = X9
      | k4_xboole_0(X10,k1_tarski(X9)) = X10 ) ),
    inference(resolution,[],[f720,f44])).

fof(f720,plain,(
    ! [X24,X23] :
      ( sP0(k1_tarski(X23),X24,X24)
      | sK4(k1_tarski(X23),X24,X24) = X23 ) ),
    inference(resolution,[],[f711,f183])).

fof(f183,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X8,k1_tarski(X7))
      | X7 = X8 ) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,(
    ! [X8,X7] :
      ( X7 = X8
      | X7 = X8
      | ~ r2_hidden(X8,k1_tarski(X7))
      | X7 = X8 ) ),
    inference(resolution,[],[f46,f76])).

fof(f76,plain,(
    ! [X0] : sP1(X0,X0,X0,k1_tarski(X0)) ),
    inference(superposition,[],[f67,f33])).

fof(f67,plain,(
    ! [X0,X1] : sP1(X1,X0,X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f60,f34])).

fof(f46,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | X1 = X5
      | X2 = X5
      | ~ r2_hidden(X5,X3)
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f711,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK4(X5,X6,X6),X5)
      | sP0(X5,X6,X6) ) ),
    inference(subsumption_resolution,[],[f708,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),X1)
      | sP0(X0,X1,X1) ) ),
    inference(factoring,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f708,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK4(X5,X6,X6),X5)
      | ~ r2_hidden(sK4(X5,X6,X6),X6)
      | sP0(X5,X6,X6) ) ),
    inference(duplicate_literal_removal,[],[f701])).

fof(f701,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK4(X5,X6,X6),X5)
      | ~ r2_hidden(sK4(X5,X6,X6),X6)
      | sP0(X5,X6,X6)
      | sP0(X5,X6,X6) ) ),
    inference(resolution,[],[f42,f99])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | sP0(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1301,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2,sK3)
      | sP0(X1,X1,k1_tarski(sK2))
      | sK3 = k4_xboole_0(sK3,k1_tarski(sK2)) ) ),
    inference(forward_demodulation,[],[f1295,f205])).

fof(f205,plain,(
    ! [X0,X1] : sK4(X0,X0,k1_tarski(X1)) = X1 ),
    inference(resolution,[],[f204,f69])).

fof(f204,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X8,k1_tarski(X7))
      | sK4(X6,X6,k1_tarski(X7)) = X7 ) ),
    inference(subsumption_resolution,[],[f202,f201])).

fof(f201,plain,(
    ! [X4,X5,X3] :
      ( sK4(X3,X3,k1_tarski(X4)) = X4
      | ~ r2_hidden(X5,k1_tarski(X4))
      | ~ r2_hidden(X5,X3) ) ),
    inference(resolution,[],[f189,f38])).

fof(f189,plain,(
    ! [X10,X9] :
      ( sP0(X10,X10,k1_tarski(X9))
      | sK4(X10,X10,k1_tarski(X9)) = X9 ) ),
    inference(resolution,[],[f183,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X0,X1),X1)
      | sP0(X0,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( sP0(X0,X0,X1)
      | r2_hidden(sK4(X0,X0,X1),X1)
      | r2_hidden(sK4(X0,X0,X1),X1)
      | sP0(X0,X0,X1) ) ),
    inference(resolution,[],[f41,f40])).

fof(f202,plain,(
    ! [X6,X8,X7] :
      ( sK4(X6,X6,k1_tarski(X7)) = X7
      | ~ r2_hidden(X8,k1_tarski(X7))
      | r2_hidden(X8,X6) ) ),
    inference(resolution,[],[f189,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1295,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(X1,X1,k1_tarski(sK2)),sK3)
      | sP0(X1,X1,k1_tarski(sK2))
      | sK3 = k4_xboole_0(sK3,k1_tarski(sK2)) ) ),
    inference(superposition,[],[f110,f1220])).

fof(f1220,plain,
    ( k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3)
    | sK3 = k4_xboole_0(sK3,k1_tarski(sK2)) ),
    inference(resolution,[],[f1219,f31])).

fof(f31,plain,
    ( ~ r2_hidden(sK2,sK3)
    | k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f18])).

% (9718)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f18,plain,
    ( ( r2_hidden(sK2,sK3)
      | k1_tarski(sK2) != k4_xboole_0(k1_tarski(sK2),sK3) )
    & ( ~ r2_hidden(sK2,sK3)
      | k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X0,X1)
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
        & ( ~ r2_hidden(X0,X1)
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( r2_hidden(sK2,sK3)
        | k1_tarski(sK2) != k4_xboole_0(k1_tarski(sK2),sK3) )
      & ( ~ r2_hidden(sK2,sK3)
        | k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f110,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(sK4(X1,X1,k4_xboole_0(X2,X3)),X3)
      | sP0(X1,X1,k4_xboole_0(X2,X3)) ) ),
    inference(resolution,[],[f108,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f38,f56])).

fof(f56,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1374,plain,(
    r2_hidden(sK2,sK3) ),
    inference(subsumption_resolution,[],[f32,f1373])).

fof(f1373,plain,(
    k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3) ),
    inference(resolution,[],[f1367,f44])).

fof(f1367,plain,(
    sP0(sK3,k1_tarski(sK2),k1_tarski(sK2)) ),
    inference(duplicate_literal_removal,[],[f1365])).

fof(f1365,plain,
    ( sP0(sK3,k1_tarski(sK2),k1_tarski(sK2))
    | sP0(sK3,k1_tarski(sK2),k1_tarski(sK2)) ),
    inference(resolution,[],[f1340,f99])).

fof(f1340,plain,(
    ! [X6] :
      ( ~ r2_hidden(sK4(sK3,X6,X6),k1_tarski(sK2))
      | sP0(sK3,X6,X6) ) ),
    inference(resolution,[],[f1320,f711])).

fof(f32,plain,
    ( k1_tarski(sK2) != k4_xboole_0(k1_tarski(sK2),sK3)
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:12:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (9701)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (9709)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (9708)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (9717)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (9699)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.56  % (9696)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (9701)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (9700)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f1376,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(subsumption_resolution,[],[f1375,f69])).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.21/0.56    inference(superposition,[],[f68,f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 0.21/0.56    inference(superposition,[],[f64,f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X1,X2))) )),
% 0.21/0.56    inference(resolution,[],[f60,f59])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ( ! [X0,X5,X3,X1] : (~sP1(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 0.21/0.56    inference(equality_resolution,[],[f47])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP1(X0,X1,X2,X3)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | (((sK5(X0,X1,X2,X3) != X0 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X2) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X0 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X2 | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK5(X0,X1,X2,X3) != X0 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X2) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X0 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X2 | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.21/0.56    inference(rectify,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 0.21/0.56    inference(flattening,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 0.21/0.56    inference(nnf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ! [X2,X1,X0,X3] : (sP1(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (sP1(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 0.21/0.57    inference(equality_resolution,[],[f54])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.57    inference(cnf_transformation,[],[f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP1(X2,X1,X0,X3)) & (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.57    inference(nnf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP1(X2,X1,X0,X3))),
% 0.21/0.57    inference(definition_folding,[],[f11,f14])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.57  fof(f1375,plain,(
% 0.21/0.57    ~r2_hidden(sK2,k1_tarski(sK2))),
% 0.21/0.57    inference(resolution,[],[f1374,f1320])).
% 0.21/0.57  fof(f1320,plain,(
% 0.21/0.57    ( ! [X3] : (~r2_hidden(X3,sK3) | ~r2_hidden(X3,k1_tarski(sK2))) )),
% 0.21/0.57    inference(superposition,[],[f82,f1308])).
% 0.21/0.57  fof(f1308,plain,(
% 0.21/0.57    sK3 = k4_xboole_0(sK3,k1_tarski(sK2))),
% 0.21/0.57    inference(resolution,[],[f1307,f69])).
% 0.21/0.57  fof(f1307,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK2)) | sK3 = k4_xboole_0(sK3,k1_tarski(sK2))) )),
% 0.21/0.57    inference(condensation,[],[f1304])).
% 0.21/0.57  fof(f1304,plain,(
% 0.21/0.57    ( ! [X2,X3] : (sK3 = k4_xboole_0(sK3,k1_tarski(sK2)) | ~r2_hidden(X2,k1_tarski(sK2)) | ~r2_hidden(X2,X3)) )),
% 0.21/0.57    inference(resolution,[],[f1302,f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.57    inference(rectify,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.57    inference(flattening,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.57    inference(nnf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.57  fof(f1302,plain,(
% 0.21/0.57    ( ! [X1] : (sP0(X1,X1,k1_tarski(sK2)) | sK3 = k4_xboole_0(sK3,k1_tarski(sK2))) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f1301,f1219])).
% 0.21/0.57  fof(f1219,plain,(
% 0.21/0.57    ( ! [X2,X3] : (r2_hidden(X2,X3) | k4_xboole_0(X3,k1_tarski(X2)) = X3) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f1218,f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.57    inference(nnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.21/0.57    inference(definition_folding,[],[f1,f12])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.57  fof(f1218,plain,(
% 0.21/0.57    ( ! [X2,X3] : (sP0(k1_tarski(X2),X3,X3) | r2_hidden(X2,X3) | k4_xboole_0(X3,k1_tarski(X2)) = X3) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f1208,f69])).
% 0.21/0.57  fof(f1208,plain,(
% 0.21/0.57    ( ! [X2,X3] : (~r2_hidden(X2,k1_tarski(X2)) | sP0(k1_tarski(X2),X3,X3) | r2_hidden(X2,X3) | k4_xboole_0(X3,k1_tarski(X2)) = X3) )),
% 0.21/0.57    inference(superposition,[],[f41,f1058])).
% 0.21/0.57  fof(f1058,plain,(
% 0.21/0.57    ( ! [X10,X9] : (sK4(k1_tarski(X9),X10,X10) = X9 | k4_xboole_0(X10,k1_tarski(X9)) = X10) )),
% 0.21/0.57    inference(resolution,[],[f720,f44])).
% 0.21/0.57  fof(f720,plain,(
% 0.21/0.57    ( ! [X24,X23] : (sP0(k1_tarski(X23),X24,X24) | sK4(k1_tarski(X23),X24,X24) = X23) )),
% 0.21/0.57    inference(resolution,[],[f711,f183])).
% 0.21/0.57  fof(f183,plain,(
% 0.21/0.57    ( ! [X8,X7] : (~r2_hidden(X8,k1_tarski(X7)) | X7 = X8) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f182])).
% 0.21/0.57  fof(f182,plain,(
% 0.21/0.57    ( ! [X8,X7] : (X7 = X8 | X7 = X8 | ~r2_hidden(X8,k1_tarski(X7)) | X7 = X8) )),
% 0.21/0.57    inference(resolution,[],[f46,f76])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    ( ! [X0] : (sP1(X0,X0,X0,k1_tarski(X0))) )),
% 0.21/0.57    inference(superposition,[],[f67,f33])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    ( ! [X0,X1] : (sP1(X1,X0,X0,k2_tarski(X0,X1))) )),
% 0.21/0.57    inference(superposition,[],[f60,f34])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X2,X0,X5,X3,X1] : (~sP1(X0,X1,X2,X3) | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3) | X0 = X5) )),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f711,plain,(
% 0.21/0.57    ( ! [X6,X5] : (r2_hidden(sK4(X5,X6,X6),X5) | sP0(X5,X6,X6)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f708,f99])).
% 0.21/0.57  fof(f99,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X1),X1) | sP0(X0,X1,X1)) )),
% 0.21/0.57    inference(factoring,[],[f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f708,plain,(
% 0.21/0.57    ( ! [X6,X5] : (r2_hidden(sK4(X5,X6,X6),X5) | ~r2_hidden(sK4(X5,X6,X6),X6) | sP0(X5,X6,X6)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f701])).
% 0.21/0.57  fof(f701,plain,(
% 0.21/0.57    ( ! [X6,X5] : (r2_hidden(sK4(X5,X6,X6),X5) | ~r2_hidden(sK4(X5,X6,X6),X6) | sP0(X5,X6,X6) | sP0(X5,X6,X6)) )),
% 0.21/0.57    inference(resolution,[],[f42,f99])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X0) | sP0(X0,X1,X2) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f1301,plain,(
% 0.21/0.57    ( ! [X1] : (~r2_hidden(sK2,sK3) | sP0(X1,X1,k1_tarski(sK2)) | sK3 = k4_xboole_0(sK3,k1_tarski(sK2))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f1295,f205])).
% 0.21/0.57  fof(f205,plain,(
% 0.21/0.57    ( ! [X0,X1] : (sK4(X0,X0,k1_tarski(X1)) = X1) )),
% 0.21/0.57    inference(resolution,[],[f204,f69])).
% 0.21/0.57  fof(f204,plain,(
% 0.21/0.57    ( ! [X6,X8,X7] : (~r2_hidden(X8,k1_tarski(X7)) | sK4(X6,X6,k1_tarski(X7)) = X7) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f202,f201])).
% 0.21/0.57  fof(f201,plain,(
% 0.21/0.57    ( ! [X4,X5,X3] : (sK4(X3,X3,k1_tarski(X4)) = X4 | ~r2_hidden(X5,k1_tarski(X4)) | ~r2_hidden(X5,X3)) )),
% 0.21/0.57    inference(resolution,[],[f189,f38])).
% 0.21/0.57  fof(f189,plain,(
% 0.21/0.57    ( ! [X10,X9] : (sP0(X10,X10,k1_tarski(X9)) | sK4(X10,X10,k1_tarski(X9)) = X9) )),
% 0.21/0.57    inference(resolution,[],[f183,f108])).
% 0.21/0.57  fof(f108,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X0,X1),X1) | sP0(X0,X0,X1)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f102])).
% 0.21/0.57  fof(f102,plain,(
% 0.21/0.57    ( ! [X0,X1] : (sP0(X0,X0,X1) | r2_hidden(sK4(X0,X0,X1),X1) | r2_hidden(sK4(X0,X0,X1),X1) | sP0(X0,X0,X1)) )),
% 0.21/0.57    inference(resolution,[],[f41,f40])).
% 0.21/0.57  fof(f202,plain,(
% 0.21/0.57    ( ! [X6,X8,X7] : (sK4(X6,X6,k1_tarski(X7)) = X7 | ~r2_hidden(X8,k1_tarski(X7)) | r2_hidden(X8,X6)) )),
% 0.21/0.57    inference(resolution,[],[f189,f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f1295,plain,(
% 0.21/0.57    ( ! [X1] : (~r2_hidden(sK4(X1,X1,k1_tarski(sK2)),sK3) | sP0(X1,X1,k1_tarski(sK2)) | sK3 = k4_xboole_0(sK3,k1_tarski(sK2))) )),
% 0.21/0.57    inference(superposition,[],[f110,f1220])).
% 0.21/0.57  fof(f1220,plain,(
% 0.21/0.57    k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3) | sK3 = k4_xboole_0(sK3,k1_tarski(sK2))),
% 0.21/0.57    inference(resolution,[],[f1219,f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ~r2_hidden(sK2,sK3) | k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3)),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  % (9718)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    (r2_hidden(sK2,sK3) | k1_tarski(sK2) != k4_xboole_0(k1_tarski(sK2),sK3)) & (~r2_hidden(sK2,sK3) | k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1))) => ((r2_hidden(sK2,sK3) | k1_tarski(sK2) != k4_xboole_0(k1_tarski(sK2),sK3)) & (~r2_hidden(sK2,sK3) | k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)))),
% 0.21/0.57    inference(nnf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,plain,(
% 0.21/0.57    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.21/0.57    inference(negated_conjecture,[],[f8])).
% 0.21/0.57  fof(f8,conjecture,(
% 0.21/0.57    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 0.21/0.57  fof(f110,plain,(
% 0.21/0.57    ( ! [X2,X3,X1] : (~r2_hidden(sK4(X1,X1,k4_xboole_0(X2,X3)),X3) | sP0(X1,X1,k4_xboole_0(X2,X3))) )),
% 0.21/0.57    inference(resolution,[],[f108,f82])).
% 0.21/0.57  fof(f82,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | ~r2_hidden(X0,X2)) )),
% 0.21/0.57    inference(resolution,[],[f38,f56])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(equality_resolution,[],[f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f1374,plain,(
% 0.21/0.57    r2_hidden(sK2,sK3)),
% 0.21/0.57    inference(subsumption_resolution,[],[f32,f1373])).
% 0.21/0.57  fof(f1373,plain,(
% 0.21/0.57    k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3)),
% 0.21/0.57    inference(resolution,[],[f1367,f44])).
% 0.21/0.57  fof(f1367,plain,(
% 0.21/0.57    sP0(sK3,k1_tarski(sK2),k1_tarski(sK2))),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f1365])).
% 0.21/0.57  fof(f1365,plain,(
% 0.21/0.57    sP0(sK3,k1_tarski(sK2),k1_tarski(sK2)) | sP0(sK3,k1_tarski(sK2),k1_tarski(sK2))),
% 0.21/0.57    inference(resolution,[],[f1340,f99])).
% 0.21/0.57  fof(f1340,plain,(
% 0.21/0.57    ( ! [X6] : (~r2_hidden(sK4(sK3,X6,X6),k1_tarski(sK2)) | sP0(sK3,X6,X6)) )),
% 0.21/0.57    inference(resolution,[],[f1320,f711])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    k1_tarski(sK2) != k4_xboole_0(k1_tarski(sK2),sK3) | r2_hidden(sK2,sK3)),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (9701)------------------------------
% 0.21/0.57  % (9701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (9701)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (9701)Memory used [KB]: 7164
% 0.21/0.57  % (9701)Time elapsed: 0.146 s
% 0.21/0.57  % (9701)------------------------------
% 0.21/0.57  % (9701)------------------------------
% 0.21/0.57  % (9695)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.57  % (9711)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.58  % (9693)Success in time 0.219 s
%------------------------------------------------------------------------------
