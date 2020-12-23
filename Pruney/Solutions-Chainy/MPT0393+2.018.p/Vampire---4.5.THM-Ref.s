%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:54 EST 2020

% Result     : Theorem 2.08s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 312 expanded)
%              Number of leaves         :   18 (  81 expanded)
%              Depth                    :   24
%              Number of atoms          :  408 (1358 expanded)
%              Number of equality atoms :  154 ( 394 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1066,plain,(
    $false ),
    inference(subsumption_resolution,[],[f49,f1065])).

fof(f1065,plain,(
    ! [X7] : k1_setfam_1(k1_tarski(X7)) = X7 ),
    inference(subsumption_resolution,[],[f1064,f562])).

fof(f562,plain,(
    ! [X1] : k1_tarski(X1) != k1_xboole_0 ),
    inference(backward_demodulation,[],[f95,f561])).

fof(f561,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(trivial_inequality_removal,[],[f550])).

fof(f550,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_tarski(X0)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) ) ),
    inference(superposition,[],[f95,f307])).

fof(f307,plain,(
    ! [X6,X5] :
      ( k1_tarski(X5) = k4_xboole_0(k1_tarski(X5),k1_tarski(X6))
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X5),k1_tarski(X6)) ) ),
    inference(resolution,[],[f304,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f304,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k1_tarski(X1)),X0) ),
    inference(duplicate_literal_removal,[],[f291])).

fof(f291,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,k1_tarski(X1)),X0)
      | r1_tarski(k4_xboole_0(X0,k1_tarski(X1)),X0) ) ),
    inference(resolution,[],[f122,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(k4_xboole_0(X0,k1_tarski(X1)),X2),X0)
      | r1_tarski(k4_xboole_0(X0,k1_tarski(X1)),X2) ) ),
    inference(resolution,[],[f83,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f95,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f1064,plain,(
    ! [X7] :
      ( k1_setfam_1(k1_tarski(X7)) = X7
      | k1_xboole_0 = k1_tarski(X7) ) ),
    inference(duplicate_literal_removal,[],[f1062])).

fof(f1062,plain,(
    ! [X7] :
      ( k1_setfam_1(k1_tarski(X7)) = X7
      | k1_setfam_1(k1_tarski(X7)) = X7
      | k1_xboole_0 = k1_tarski(X7) ) ),
    inference(resolution,[],[f1058,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_setfam_1(X0) = X1
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f53,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( sP1(X1,X0)
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( sP1(X1,X0)
        | k1_xboole_0 = X0 ) ) ),
    inference(definition_folding,[],[f14,f17,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ! [X3] :
              ( r2_hidden(X2,X3)
              | ~ r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ( k1_setfam_1(X0) = X1
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f14,plain,(
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

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | k1_setfam_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X1) = X0
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | k1_setfam_1(X1) != X0 ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ( ( k1_setfam_1(X0) = X1
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | k1_setfam_1(X0) != X1 ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f1058,plain,(
    ! [X1] :
      ( sP0(k1_tarski(X1),X1)
      | k1_setfam_1(k1_tarski(X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f1057,f372])).

fof(f372,plain,(
    ! [X14,X13] :
      ( r2_hidden(sK4(k1_tarski(X13),X14),X13)
      | sP0(k1_tarski(X13),X14)
      | r2_hidden(sK4(k1_tarski(X13),X14),X14) ) ),
    inference(resolution,[],[f57,f104])).

fof(f104,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(resolution,[],[f96,f102])).

fof(f102,plain,(
    ! [X0] : sP2(X0,X0,k1_tarski(X0)) ),
    inference(superposition,[],[f98,f50])).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f98,plain,(
    ! [X0,X1] : sP2(X1,X0,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP2(X1,X0,X2) )
      & ( sP2(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP2(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f19])).

fof(f19,plain,(
    ! [X1,X0,X2] :
      ( sP2(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f96,plain,(
    ! [X4,X2,X1] :
      ( ~ sP2(X4,X1,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ( sK8(X0,X1,X2) != X0
              & sK8(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( sK8(X0,X1,X2) = X0
            | sK8(X0,X1,X2) = X1
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK8(X0,X1,X2) != X0
            & sK8(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( sK8(X0,X1,X2) = X0
          | sK8(X0,X1,X2) = X1
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
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
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
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
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | r2_hidden(sK4(X0,X1),X4)
      | sP0(X0,X1)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ( ~ r2_hidden(sK4(X0,X1),sK5(X0,X1))
              & r2_hidden(sK5(X0,X1),X0) )
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( ! [X4] :
                ( r2_hidden(sK4(X0,X1),X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ( ~ r2_hidden(X5,sK6(X0,X5))
                & r2_hidden(sK6(X0,X5),X0) ) )
            & ( ! [X7] :
                  ( r2_hidden(X5,X7)
                  | ~ r2_hidden(X7,X0) )
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f26,f29,f28,f27])).

fof(f27,plain,(
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
              ( ~ r2_hidden(sK4(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK4(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(sK4(X0,X1),X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK6(X0,X5))
        & r2_hidden(sK6(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

% (13766)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
fof(f1057,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(k1_tarski(X1),X1),X1)
      | sP0(k1_tarski(X1),X1)
      | k1_setfam_1(k1_tarski(X1)) = X1 ) ),
    inference(duplicate_literal_removal,[],[f1056])).

fof(f1056,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(k1_tarski(X1),X1),X1)
      | sP0(k1_tarski(X1),X1)
      | ~ r2_hidden(sK4(k1_tarski(X1),X1),X1)
      | k1_setfam_1(k1_tarski(X1)) = X1 ) ),
    inference(superposition,[],[f59,f1053])).

fof(f1053,plain,(
    ! [X7] :
      ( sK5(k1_tarski(X7),X7) = X7
      | k1_setfam_1(k1_tarski(X7)) = X7 ) ),
    inference(subsumption_resolution,[],[f1051,f562])).

fof(f1051,plain,(
    ! [X7] :
      ( sK5(k1_tarski(X7),X7) = X7
      | k1_setfam_1(k1_tarski(X7)) = X7
      | k1_xboole_0 = k1_tarski(X7) ) ),
    inference(resolution,[],[f1044,f125])).

fof(f1044,plain,(
    ! [X6] :
      ( sP0(k1_tarski(X6),X6)
      | sK5(k1_tarski(X6),X6) = X6 ) ),
    inference(resolution,[],[f1039,f133])).

fof(f133,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k1_tarski(X4))
      | X4 = X5 ) ),
    inference(superposition,[],[f99,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f99,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1039,plain,(
    ! [X9] :
      ( r2_hidden(sK5(k1_tarski(X9),X9),k1_tarski(X9))
      | sP0(k1_tarski(X9),X9) ) ),
    inference(subsumption_resolution,[],[f1035,f563])).

fof(f563,plain,(
    ! [X0] : ~ r1_tarski(k1_tarski(X0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f115,f562])).

fof(f115,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(X0),k1_xboole_0)
      | k1_tarski(X0) = k1_xboole_0 ) ),
    inference(resolution,[],[f65,f94])).

fof(f94,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1035,plain,(
    ! [X9] :
      ( r2_hidden(sK5(k1_tarski(X9),X9),k1_tarski(X9))
      | r1_tarski(k1_tarski(X9),k1_xboole_0)
      | sP0(k1_tarski(X9),X9) ) ),
    inference(superposition,[],[f947,f212])).

fof(f212,plain,(
    ! [X0] : sK7(k1_tarski(X0),k1_xboole_0) = X0 ),
    inference(condensation,[],[f209])).

fof(f209,plain,(
    ! [X4,X3] :
      ( sK7(k1_tarski(X3),k1_xboole_0) = X3
      | X3 = X4 ) ),
    inference(resolution,[],[f196,f133])).

fof(f196,plain,(
    ! [X14,X15] :
      ( r2_hidden(X14,k1_tarski(X15))
      | sK7(k1_tarski(X14),k1_xboole_0) = X14 ) ),
    inference(resolution,[],[f186,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,k1_tarski(X1)) ) ),
    inference(resolution,[],[f66,f94])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f186,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | sK7(k1_tarski(X0),X1) = X0 ) ),
    inference(resolution,[],[f141,f104])).

fof(f141,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X3,k1_tarski(X1))
      | sK7(k1_tarski(X1),X2) = X1
      | r2_hidden(X3,X2) ) ),
    inference(resolution,[],[f136,f66])).

fof(f136,plain,(
    ! [X4,X3] :
      ( r1_tarski(k1_tarski(X3),X4)
      | sK7(k1_tarski(X3),X4) = X3 ) ),
    inference(resolution,[],[f133,f67])).

fof(f947,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,sK7(X0,X1)),X0)
      | r1_tarski(X0,X1)
      | sP0(X0,sK7(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f946,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f946,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,sK7(X0,X1)),sK7(X0,X1))
      | sP0(X0,sK7(X0,X1))
      | r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,sK7(X0,X1)),X0) ) ),
    inference(duplicate_literal_removal,[],[f921])).

fof(f921,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,sK7(X0,X1)),sK7(X0,X1))
      | sP0(X0,sK7(X0,X1))
      | r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,sK7(X0,X1)),X0)
      | sP0(X0,sK7(X0,X1)) ) ),
    inference(resolution,[],[f374,f58])).

fof(f374,plain,(
    ! [X21,X19,X20] :
      ( r2_hidden(sK4(X19,X20),sK7(X19,X21))
      | r2_hidden(sK4(X19,X20),X20)
      | sP0(X19,X20)
      | r1_tarski(X19,X21) ) ),
    inference(resolution,[],[f57,f67])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),sK5(X0,X1))
      | sP0(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    sK3 != k1_setfam_1(k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    sK3 != k1_setfam_1(k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f21])).

fof(f21,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => sK3 != k1_setfam_1(k1_tarski(sK3)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:21:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (13731)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (13733)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (13734)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (13731)Refutation not found, incomplete strategy% (13731)------------------------------
% 0.22/0.52  % (13731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13729)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (13731)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (13731)Memory used [KB]: 10746
% 0.22/0.52  % (13731)Time elapsed: 0.094 s
% 0.22/0.52  % (13731)------------------------------
% 0.22/0.52  % (13731)------------------------------
% 0.22/0.53  % (13755)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (13739)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (13735)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (13739)Refutation not found, incomplete strategy% (13739)------------------------------
% 0.22/0.53  % (13739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13739)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (13739)Memory used [KB]: 10618
% 0.22/0.53  % (13739)Time elapsed: 0.117 s
% 0.22/0.53  % (13739)------------------------------
% 0.22/0.53  % (13739)------------------------------
% 0.22/0.53  % (13741)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (13754)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (13730)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (13736)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (13732)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (13752)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (13745)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (13751)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (13757)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (13738)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (13753)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (13743)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (13744)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (13746)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (13748)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (13758)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (13749)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (13749)Refutation not found, incomplete strategy% (13749)------------------------------
% 0.22/0.55  % (13749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (13749)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (13749)Memory used [KB]: 10746
% 0.22/0.55  % (13749)Time elapsed: 0.126 s
% 0.22/0.55  % (13749)------------------------------
% 0.22/0.55  % (13749)------------------------------
% 0.22/0.55  % (13737)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (13737)Refutation not found, incomplete strategy% (13737)------------------------------
% 0.22/0.56  % (13737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (13737)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (13737)Memory used [KB]: 10618
% 0.22/0.56  % (13737)Time elapsed: 0.139 s
% 0.22/0.56  % (13737)------------------------------
% 0.22/0.56  % (13737)------------------------------
% 0.22/0.56  % (13750)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (13740)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (13750)Refutation not found, incomplete strategy% (13750)------------------------------
% 0.22/0.56  % (13750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (13750)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (13750)Memory used [KB]: 1663
% 0.22/0.56  % (13750)Time elapsed: 0.142 s
% 0.22/0.56  % (13750)------------------------------
% 0.22/0.56  % (13750)------------------------------
% 0.22/0.56  % (13747)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.51/0.56  % (13756)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.51/0.57  % (13746)Refutation not found, incomplete strategy% (13746)------------------------------
% 1.51/0.57  % (13746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (13746)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.57  
% 1.51/0.57  % (13746)Memory used [KB]: 10618
% 1.51/0.57  % (13746)Time elapsed: 0.148 s
% 1.51/0.57  % (13746)------------------------------
% 1.51/0.57  % (13746)------------------------------
% 1.51/0.57  % (13742)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.00/0.63  % (13764)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.00/0.64  % (13765)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.08/0.67  % (13736)Refutation found. Thanks to Tanya!
% 2.08/0.67  % SZS status Theorem for theBenchmark
% 2.08/0.67  % SZS output start Proof for theBenchmark
% 2.08/0.67  fof(f1066,plain,(
% 2.08/0.67    $false),
% 2.08/0.67    inference(subsumption_resolution,[],[f49,f1065])).
% 2.08/0.67  fof(f1065,plain,(
% 2.08/0.67    ( ! [X7] : (k1_setfam_1(k1_tarski(X7)) = X7) )),
% 2.08/0.67    inference(subsumption_resolution,[],[f1064,f562])).
% 2.08/0.67  fof(f562,plain,(
% 2.08/0.67    ( ! [X1] : (k1_tarski(X1) != k1_xboole_0) )),
% 2.08/0.67    inference(backward_demodulation,[],[f95,f561])).
% 2.08/0.67  fof(f561,plain,(
% 2.08/0.67    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 2.08/0.67    inference(trivial_inequality_removal,[],[f550])).
% 2.08/0.67  fof(f550,plain,(
% 2.08/0.67    ( ! [X0] : (k1_tarski(X0) != k1_tarski(X0) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 2.08/0.67    inference(superposition,[],[f95,f307])).
% 2.08/0.67  fof(f307,plain,(
% 2.08/0.67    ( ! [X6,X5] : (k1_tarski(X5) = k4_xboole_0(k1_tarski(X5),k1_tarski(X6)) | k1_xboole_0 = k4_xboole_0(k1_tarski(X5),k1_tarski(X6))) )),
% 2.08/0.67    inference(resolution,[],[f304,f69])).
% 2.08/0.67  fof(f69,plain,(
% 2.08/0.67    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 2.08/0.67    inference(cnf_transformation,[],[f39])).
% 2.08/0.67  fof(f39,plain,(
% 2.08/0.67    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.08/0.67    inference(flattening,[],[f38])).
% 2.08/0.67  fof(f38,plain,(
% 2.08/0.67    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.08/0.67    inference(nnf_transformation,[],[f7])).
% 2.08/0.67  fof(f7,axiom,(
% 2.08/0.67    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.08/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.08/0.67  fof(f304,plain,(
% 2.08/0.67    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k1_tarski(X1)),X0)) )),
% 2.08/0.67    inference(duplicate_literal_removal,[],[f291])).
% 2.08/0.67  fof(f291,plain,(
% 2.08/0.67    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k1_tarski(X1)),X0) | r1_tarski(k4_xboole_0(X0,k1_tarski(X1)),X0)) )),
% 2.08/0.67    inference(resolution,[],[f122,f68])).
% 2.08/0.67  fof(f68,plain,(
% 2.08/0.67    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.08/0.67    inference(cnf_transformation,[],[f37])).
% 2.08/0.67  fof(f37,plain,(
% 2.08/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.08/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f36])).
% 2.08/0.67  fof(f36,plain,(
% 2.08/0.67    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 2.08/0.67    introduced(choice_axiom,[])).
% 2.08/0.67  fof(f35,plain,(
% 2.08/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.08/0.67    inference(rectify,[],[f34])).
% 2.08/0.67  fof(f34,plain,(
% 2.08/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.08/0.67    inference(nnf_transformation,[],[f15])).
% 2.08/0.67  fof(f15,plain,(
% 2.08/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.08/0.67    inference(ennf_transformation,[],[f1])).
% 2.08/0.67  fof(f1,axiom,(
% 2.08/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.08/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.08/0.67  fof(f122,plain,(
% 2.08/0.67    ( ! [X2,X0,X1] : (r2_hidden(sK7(k4_xboole_0(X0,k1_tarski(X1)),X2),X0) | r1_tarski(k4_xboole_0(X0,k1_tarski(X1)),X2)) )),
% 2.08/0.67    inference(resolution,[],[f83,f67])).
% 2.08/0.67  fof(f67,plain,(
% 2.08/0.67    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.08/0.67    inference(cnf_transformation,[],[f37])).
% 2.08/0.67  fof(f83,plain,(
% 2.08/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | r2_hidden(X0,X1)) )),
% 2.08/0.67    inference(cnf_transformation,[],[f48])).
% 2.08/0.67  fof(f48,plain,(
% 2.08/0.67    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 2.08/0.67    inference(flattening,[],[f47])).
% 2.08/0.67  fof(f47,plain,(
% 2.08/0.67    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 2.08/0.67    inference(nnf_transformation,[],[f9])).
% 2.08/0.67  fof(f9,axiom,(
% 2.08/0.67    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 2.08/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 2.08/0.67  fof(f95,plain,(
% 2.08/0.67    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 2.08/0.67    inference(equality_resolution,[],[f72])).
% 2.08/0.67  fof(f72,plain,(
% 2.08/0.67    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 2.08/0.67    inference(cnf_transformation,[],[f40])).
% 2.08/0.67  fof(f40,plain,(
% 2.08/0.67    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 2.08/0.67    inference(nnf_transformation,[],[f8])).
% 2.08/0.67  fof(f8,axiom,(
% 2.08/0.67    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 2.08/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 2.08/0.67  fof(f1064,plain,(
% 2.08/0.67    ( ! [X7] : (k1_setfam_1(k1_tarski(X7)) = X7 | k1_xboole_0 = k1_tarski(X7)) )),
% 2.08/0.67    inference(duplicate_literal_removal,[],[f1062])).
% 2.08/0.67  fof(f1062,plain,(
% 2.08/0.67    ( ! [X7] : (k1_setfam_1(k1_tarski(X7)) = X7 | k1_setfam_1(k1_tarski(X7)) = X7 | k1_xboole_0 = k1_tarski(X7)) )),
% 2.08/0.67    inference(resolution,[],[f1058,f125])).
% 2.08/0.67  fof(f125,plain,(
% 2.08/0.67    ( ! [X0,X1] : (~sP0(X0,X1) | k1_setfam_1(X0) = X1 | k1_xboole_0 = X0) )),
% 2.08/0.67    inference(resolution,[],[f53,f60])).
% 2.08/0.67  fof(f60,plain,(
% 2.08/0.67    ( ! [X0,X1] : (sP1(X1,X0) | k1_xboole_0 = X0) )),
% 2.08/0.67    inference(cnf_transformation,[],[f31])).
% 2.08/0.67  fof(f31,plain,(
% 2.08/0.67    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (sP1(X1,X0) | k1_xboole_0 = X0))),
% 2.08/0.67    inference(nnf_transformation,[],[f18])).
% 2.08/0.67  fof(f18,plain,(
% 2.08/0.67    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & (sP1(X1,X0) | k1_xboole_0 = X0))),
% 2.08/0.67    inference(definition_folding,[],[f14,f17,f16])).
% 2.08/0.67  fof(f16,plain,(
% 2.08/0.67    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0))))),
% 2.08/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.08/0.67  fof(f17,plain,(
% 2.08/0.67    ! [X1,X0] : ((k1_setfam_1(X0) = X1 <=> sP0(X0,X1)) | ~sP1(X1,X0))),
% 2.08/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.08/0.67  fof(f14,plain,(
% 2.08/0.67    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 2.08/0.67    inference(ennf_transformation,[],[f10])).
% 2.08/0.67  fof(f10,axiom,(
% 2.08/0.67    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 2.08/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).
% 2.08/0.67  fof(f53,plain,(
% 2.08/0.67    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | k1_setfam_1(X1) = X0) )),
% 2.08/0.67    inference(cnf_transformation,[],[f24])).
% 2.08/0.67  fof(f24,plain,(
% 2.08/0.67    ! [X0,X1] : (((k1_setfam_1(X1) = X0 | ~sP0(X1,X0)) & (sP0(X1,X0) | k1_setfam_1(X1) != X0)) | ~sP1(X0,X1))),
% 2.08/0.67    inference(rectify,[],[f23])).
% 2.08/0.67  fof(f23,plain,(
% 2.08/0.67    ! [X1,X0] : (((k1_setfam_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_setfam_1(X0) != X1)) | ~sP1(X1,X0))),
% 2.08/0.67    inference(nnf_transformation,[],[f17])).
% 2.08/0.67  fof(f1058,plain,(
% 2.08/0.67    ( ! [X1] : (sP0(k1_tarski(X1),X1) | k1_setfam_1(k1_tarski(X1)) = X1) )),
% 2.08/0.67    inference(subsumption_resolution,[],[f1057,f372])).
% 2.08/0.67  fof(f372,plain,(
% 2.08/0.67    ( ! [X14,X13] : (r2_hidden(sK4(k1_tarski(X13),X14),X13) | sP0(k1_tarski(X13),X14) | r2_hidden(sK4(k1_tarski(X13),X14),X14)) )),
% 2.08/0.67    inference(resolution,[],[f57,f104])).
% 2.08/0.67  fof(f104,plain,(
% 2.08/0.67    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 2.08/0.67    inference(resolution,[],[f96,f102])).
% 2.08/0.67  fof(f102,plain,(
% 2.08/0.67    ( ! [X0] : (sP2(X0,X0,k1_tarski(X0))) )),
% 2.08/0.67    inference(superposition,[],[f98,f50])).
% 2.08/0.67  fof(f50,plain,(
% 2.08/0.67    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.08/0.67    inference(cnf_transformation,[],[f4])).
% 2.08/0.67  fof(f4,axiom,(
% 2.08/0.67    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.08/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.08/0.67  fof(f98,plain,(
% 2.08/0.67    ( ! [X0,X1] : (sP2(X1,X0,k2_tarski(X0,X1))) )),
% 2.08/0.67    inference(equality_resolution,[],[f81])).
% 2.08/0.67  fof(f81,plain,(
% 2.08/0.67    ( ! [X2,X0,X1] : (sP2(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 2.08/0.67    inference(cnf_transformation,[],[f46])).
% 2.08/0.67  fof(f46,plain,(
% 2.08/0.67    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP2(X1,X0,X2)) & (sP2(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 2.08/0.67    inference(nnf_transformation,[],[f20])).
% 2.08/0.67  fof(f20,plain,(
% 2.08/0.67    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP2(X1,X0,X2))),
% 2.08/0.67    inference(definition_folding,[],[f3,f19])).
% 2.08/0.67  fof(f19,plain,(
% 2.08/0.67    ! [X1,X0,X2] : (sP2(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.08/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.08/0.67  fof(f3,axiom,(
% 2.08/0.67    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.08/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 2.08/0.67  fof(f96,plain,(
% 2.08/0.67    ( ! [X4,X2,X1] : (~sP2(X4,X1,X2) | r2_hidden(X4,X2)) )),
% 2.08/0.67    inference(equality_resolution,[],[f77])).
% 2.08/0.67  fof(f77,plain,(
% 2.08/0.67    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | ~sP2(X0,X1,X2)) )),
% 2.08/0.67    inference(cnf_transformation,[],[f45])).
% 2.08/0.67  fof(f45,plain,(
% 2.08/0.67    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (((sK8(X0,X1,X2) != X0 & sK8(X0,X1,X2) != X1) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X0 | sK8(X0,X1,X2) = X1 | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 2.08/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f43,f44])).
% 2.08/0.67  fof(f44,plain,(
% 2.08/0.67    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK8(X0,X1,X2) != X0 & sK8(X0,X1,X2) != X1) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X0 | sK8(X0,X1,X2) = X1 | r2_hidden(sK8(X0,X1,X2),X2))))),
% 2.08/0.67    introduced(choice_axiom,[])).
% 2.08/0.67  fof(f43,plain,(
% 2.08/0.67    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 2.08/0.67    inference(rectify,[],[f42])).
% 2.08/0.67  fof(f42,plain,(
% 2.08/0.67    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 2.08/0.67    inference(flattening,[],[f41])).
% 2.08/0.67  fof(f41,plain,(
% 2.08/0.67    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 2.08/0.67    inference(nnf_transformation,[],[f19])).
% 2.08/0.67  fof(f57,plain,(
% 2.08/0.67    ( ! [X4,X0,X1] : (~r2_hidden(X4,X0) | r2_hidden(sK4(X0,X1),X4) | sP0(X0,X1) | r2_hidden(sK4(X0,X1),X1)) )),
% 2.08/0.67    inference(cnf_transformation,[],[f30])).
% 2.08/0.67  fof(f30,plain,(
% 2.08/0.67    ! [X0,X1] : ((sP0(X0,X1) | (((~r2_hidden(sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)) | ~r2_hidden(sK4(X0,X1),X1)) & (! [X4] : (r2_hidden(sK4(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK6(X0,X5)) & r2_hidden(sK6(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 2.08/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f26,f29,f28,f27])).
% 2.08/0.67  fof(f27,plain,(
% 2.08/0.67    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK4(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK4(X0,X1),X1)) & (! [X4] : (r2_hidden(sK4(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK4(X0,X1),X1))))),
% 2.08/0.67    introduced(choice_axiom,[])).
% 2.08/0.67  fof(f28,plain,(
% 2.08/0.67    ! [X1,X0] : (? [X3] : (~r2_hidden(sK4(X0,X1),X3) & r2_hidden(X3,X0)) => (~r2_hidden(sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)))),
% 2.08/0.67    introduced(choice_axiom,[])).
% 2.08/0.67  fof(f29,plain,(
% 2.08/0.67    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK6(X0,X5)) & r2_hidden(sK6(X0,X5),X0)))),
% 2.08/0.67    introduced(choice_axiom,[])).
% 2.08/0.67  fof(f26,plain,(
% 2.08/0.67    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 2.08/0.67    inference(rectify,[],[f25])).
% 2.08/0.67  fof(f25,plain,(
% 2.08/0.67    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 2.08/0.67    inference(nnf_transformation,[],[f16])).
% 2.08/0.69  % (13766)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.08/0.69  fof(f1057,plain,(
% 2.08/0.69    ( ! [X1] : (~r2_hidden(sK4(k1_tarski(X1),X1),X1) | sP0(k1_tarski(X1),X1) | k1_setfam_1(k1_tarski(X1)) = X1) )),
% 2.08/0.69    inference(duplicate_literal_removal,[],[f1056])).
% 2.08/0.69  fof(f1056,plain,(
% 2.08/0.69    ( ! [X1] : (~r2_hidden(sK4(k1_tarski(X1),X1),X1) | sP0(k1_tarski(X1),X1) | ~r2_hidden(sK4(k1_tarski(X1),X1),X1) | k1_setfam_1(k1_tarski(X1)) = X1) )),
% 2.08/0.69    inference(superposition,[],[f59,f1053])).
% 2.08/0.69  fof(f1053,plain,(
% 2.08/0.69    ( ! [X7] : (sK5(k1_tarski(X7),X7) = X7 | k1_setfam_1(k1_tarski(X7)) = X7) )),
% 2.08/0.69    inference(subsumption_resolution,[],[f1051,f562])).
% 2.08/0.69  fof(f1051,plain,(
% 2.08/0.69    ( ! [X7] : (sK5(k1_tarski(X7),X7) = X7 | k1_setfam_1(k1_tarski(X7)) = X7 | k1_xboole_0 = k1_tarski(X7)) )),
% 2.08/0.69    inference(resolution,[],[f1044,f125])).
% 2.08/0.69  fof(f1044,plain,(
% 2.08/0.69    ( ! [X6] : (sP0(k1_tarski(X6),X6) | sK5(k1_tarski(X6),X6) = X6) )),
% 2.08/0.69    inference(resolution,[],[f1039,f133])).
% 2.08/0.69  fof(f133,plain,(
% 2.08/0.69    ( ! [X4,X5] : (~r2_hidden(X5,k1_tarski(X4)) | X4 = X5) )),
% 2.08/0.69    inference(superposition,[],[f99,f73])).
% 2.08/0.69  fof(f73,plain,(
% 2.08/0.69    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 2.08/0.69    inference(cnf_transformation,[],[f40])).
% 2.08/0.69  fof(f99,plain,(
% 2.08/0.69    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 2.08/0.69    inference(equality_resolution,[],[f84])).
% 2.08/0.69  fof(f84,plain,(
% 2.08/0.69    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 2.08/0.69    inference(cnf_transformation,[],[f48])).
% 2.08/0.69  fof(f1039,plain,(
% 2.08/0.69    ( ! [X9] : (r2_hidden(sK5(k1_tarski(X9),X9),k1_tarski(X9)) | sP0(k1_tarski(X9),X9)) )),
% 2.08/0.69    inference(subsumption_resolution,[],[f1035,f563])).
% 2.08/0.69  fof(f563,plain,(
% 2.08/0.69    ( ! [X0] : (~r1_tarski(k1_tarski(X0),k1_xboole_0)) )),
% 2.08/0.69    inference(subsumption_resolution,[],[f115,f562])).
% 2.08/0.69  fof(f115,plain,(
% 2.08/0.69    ( ! [X0] : (~r1_tarski(k1_tarski(X0),k1_xboole_0) | k1_tarski(X0) = k1_xboole_0) )),
% 2.08/0.69    inference(resolution,[],[f65,f94])).
% 2.08/0.69  fof(f94,plain,(
% 2.08/0.69    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 2.08/0.69    inference(equality_resolution,[],[f70])).
% 2.08/0.69  fof(f70,plain,(
% 2.08/0.69    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 2.08/0.69    inference(cnf_transformation,[],[f39])).
% 2.08/0.69  fof(f65,plain,(
% 2.08/0.69    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.08/0.69    inference(cnf_transformation,[],[f33])).
% 2.08/0.69  fof(f33,plain,(
% 2.08/0.69    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.08/0.69    inference(flattening,[],[f32])).
% 2.08/0.69  fof(f32,plain,(
% 2.08/0.69    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.08/0.69    inference(nnf_transformation,[],[f2])).
% 2.08/0.69  fof(f2,axiom,(
% 2.08/0.69    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.08/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.08/0.69  fof(f1035,plain,(
% 2.08/0.69    ( ! [X9] : (r2_hidden(sK5(k1_tarski(X9),X9),k1_tarski(X9)) | r1_tarski(k1_tarski(X9),k1_xboole_0) | sP0(k1_tarski(X9),X9)) )),
% 2.08/0.69    inference(superposition,[],[f947,f212])).
% 2.08/0.69  fof(f212,plain,(
% 2.08/0.69    ( ! [X0] : (sK7(k1_tarski(X0),k1_xboole_0) = X0) )),
% 2.08/0.69    inference(condensation,[],[f209])).
% 2.08/0.69  fof(f209,plain,(
% 2.08/0.69    ( ! [X4,X3] : (sK7(k1_tarski(X3),k1_xboole_0) = X3 | X3 = X4) )),
% 2.08/0.69    inference(resolution,[],[f196,f133])).
% 2.08/0.69  fof(f196,plain,(
% 2.08/0.69    ( ! [X14,X15] : (r2_hidden(X14,k1_tarski(X15)) | sK7(k1_tarski(X14),k1_xboole_0) = X14) )),
% 2.08/0.69    inference(resolution,[],[f186,f117])).
% 2.08/0.69  fof(f117,plain,(
% 2.08/0.69    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,k1_tarski(X1))) )),
% 2.08/0.69    inference(resolution,[],[f66,f94])).
% 2.08/0.69  fof(f66,plain,(
% 2.08/0.69    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 2.08/0.69    inference(cnf_transformation,[],[f37])).
% 2.08/0.69  fof(f186,plain,(
% 2.08/0.69    ( ! [X0,X1] : (r2_hidden(X0,X1) | sK7(k1_tarski(X0),X1) = X0) )),
% 2.08/0.69    inference(resolution,[],[f141,f104])).
% 2.08/0.69  fof(f141,plain,(
% 2.08/0.69    ( ! [X2,X3,X1] : (~r2_hidden(X3,k1_tarski(X1)) | sK7(k1_tarski(X1),X2) = X1 | r2_hidden(X3,X2)) )),
% 2.08/0.69    inference(resolution,[],[f136,f66])).
% 2.08/0.69  fof(f136,plain,(
% 2.08/0.69    ( ! [X4,X3] : (r1_tarski(k1_tarski(X3),X4) | sK7(k1_tarski(X3),X4) = X3) )),
% 2.08/0.69    inference(resolution,[],[f133,f67])).
% 2.08/0.69  fof(f947,plain,(
% 2.08/0.69    ( ! [X0,X1] : (r2_hidden(sK5(X0,sK7(X0,X1)),X0) | r1_tarski(X0,X1) | sP0(X0,sK7(X0,X1))) )),
% 2.08/0.69    inference(subsumption_resolution,[],[f946,f58])).
% 2.08/0.69  fof(f58,plain,(
% 2.08/0.69    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0) | sP0(X0,X1)) )),
% 2.08/0.69    inference(cnf_transformation,[],[f30])).
% 2.08/0.69  fof(f946,plain,(
% 2.08/0.69    ( ! [X0,X1] : (r2_hidden(sK4(X0,sK7(X0,X1)),sK7(X0,X1)) | sP0(X0,sK7(X0,X1)) | r1_tarski(X0,X1) | r2_hidden(sK5(X0,sK7(X0,X1)),X0)) )),
% 2.08/0.69    inference(duplicate_literal_removal,[],[f921])).
% 2.08/0.69  fof(f921,plain,(
% 2.08/0.69    ( ! [X0,X1] : (r2_hidden(sK4(X0,sK7(X0,X1)),sK7(X0,X1)) | sP0(X0,sK7(X0,X1)) | r1_tarski(X0,X1) | r2_hidden(sK5(X0,sK7(X0,X1)),X0) | sP0(X0,sK7(X0,X1))) )),
% 2.08/0.69    inference(resolution,[],[f374,f58])).
% 2.08/0.69  fof(f374,plain,(
% 2.08/0.69    ( ! [X21,X19,X20] : (r2_hidden(sK4(X19,X20),sK7(X19,X21)) | r2_hidden(sK4(X19,X20),X20) | sP0(X19,X20) | r1_tarski(X19,X21)) )),
% 2.08/0.69    inference(resolution,[],[f57,f67])).
% 2.08/0.69  fof(f59,plain,(
% 2.08/0.69    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),sK5(X0,X1)) | sP0(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 2.08/0.69    inference(cnf_transformation,[],[f30])).
% 2.08/0.69  fof(f49,plain,(
% 2.08/0.69    sK3 != k1_setfam_1(k1_tarski(sK3))),
% 2.08/0.69    inference(cnf_transformation,[],[f22])).
% 2.08/0.69  fof(f22,plain,(
% 2.08/0.69    sK3 != k1_setfam_1(k1_tarski(sK3))),
% 2.08/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f21])).
% 2.08/0.69  fof(f21,plain,(
% 2.08/0.69    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => sK3 != k1_setfam_1(k1_tarski(sK3))),
% 2.08/0.69    introduced(choice_axiom,[])).
% 2.08/0.69  fof(f13,plain,(
% 2.08/0.69    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 2.08/0.69    inference(ennf_transformation,[],[f12])).
% 2.08/0.69  fof(f12,negated_conjecture,(
% 2.08/0.69    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.08/0.69    inference(negated_conjecture,[],[f11])).
% 2.08/0.69  fof(f11,conjecture,(
% 2.08/0.69    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.08/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 2.08/0.69  % SZS output end Proof for theBenchmark
% 2.08/0.69  % (13736)------------------------------
% 2.08/0.69  % (13736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.69  % (13736)Termination reason: Refutation
% 2.08/0.69  
% 2.08/0.69  % (13736)Memory used [KB]: 7291
% 2.08/0.69  % (13736)Time elapsed: 0.216 s
% 2.08/0.69  % (13736)------------------------------
% 2.08/0.69  % (13736)------------------------------
% 2.08/0.69  % (13728)Success in time 0.321 s
%------------------------------------------------------------------------------
