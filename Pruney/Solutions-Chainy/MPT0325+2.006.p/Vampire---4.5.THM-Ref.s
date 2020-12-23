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
% DateTime   : Thu Dec  3 12:42:38 EST 2020

% Result     : Theorem 1.78s
% Output     : Refutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 306 expanded)
%              Number of leaves         :   13 (  76 expanded)
%              Depth                    :   21
%              Number of atoms          :  269 (1328 expanded)
%              Number of equality atoms :   65 ( 168 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1315,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1261,f73])).

fof(f73,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1261,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f41,f1259])).

fof(f1259,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f1226,f72])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1226,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f41,f1224])).

fof(f1224,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f1218,f1072])).

fof(f1072,plain,
    ( ~ r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f1053,f42])).

fof(f42,plain,
    ( ~ r1_tarski(sK2,sK4)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r1_tarski(sK2,sK4)
      | ~ r1_tarski(sK1,sK3) )
    & k1_xboole_0 != k2_zfmisc_1(sK1,sK2)
    & r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f16,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK2,sK4)
        | ~ r1_tarski(sK1,sK3) )
      & k1_xboole_0 != k2_zfmisc_1(sK1,sK2)
      & r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f1053,plain,
    ( r1_tarski(sK2,sK4)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f257,f1016])).

fof(f1016,plain,
    ( sK2 = k3_xboole_0(sK2,sK4)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f1004,f160])).

fof(f160,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,k3_xboole_0(X6,X7))
      | k3_xboole_0(X6,X7) = X6 ) ),
    inference(resolution,[],[f157,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f157,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X0)
      | r1_tarski(k3_xboole_0(X0,X1),X0) ) ),
    inference(resolution,[],[f139,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(k3_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f112,f74])).

fof(f74,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f22])).

fof(f22,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X3,X2,X0)
      | r2_hidden(sK5(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f59,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK6(X0,X1,X2),X0)
              & r2_hidden(sK6(X0,X1,X2),X1) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f1004,plain,
    ( r1_tarski(sK2,k3_xboole_0(sK2,sK4))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f976,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f976,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,k3_xboole_0(sK2,sK4))) ),
    inference(superposition,[],[f426,f89])).

fof(f89,plain,(
    k2_zfmisc_1(sK1,sK2) = k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f47,f40])).

fof(f40,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f426,plain,(
    ! [X6,X4,X7,X5] : r1_tarski(k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)),k2_zfmisc_1(X4,k3_xboole_0(X6,X7))) ),
    inference(superposition,[],[f159,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f159,plain,(
    ! [X4,X5,X3] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X3,X4),X5),k2_zfmisc_1(X3,X5)) ),
    inference(resolution,[],[f157,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f257,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(duplicate_literal_removal,[],[f247])).

fof(f247,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X1)
      | r1_tarski(k3_xboole_0(X0,X1),X1) ) ),
    inference(resolution,[],[f144,f53])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(k3_xboole_0(X0,X1),X2),X1)
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f113,f74])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X2,X3,X0)
      | r2_hidden(sK5(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f60,f52])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1218,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f1033,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1033,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK2))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f929,f1016])).

fof(f929,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4))) ),
    inference(superposition,[],[f425,f89])).

fof(f425,plain,(
    ! [X2,X0,X3,X1] : r1_tarski(k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k2_zfmisc_1(X1,k3_xboole_0(X2,X3))) ),
    inference(superposition,[],[f259,f69])).

fof(f259,plain,(
    ! [X4,X5,X3] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X3,X4),X5),k2_zfmisc_1(X4,X5)) ),
    inference(resolution,[],[f257,f57])).

fof(f41,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:53:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (28316)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (28332)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (28323)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (28319)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (28326)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (28327)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (28335)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (28313)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (28314)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (28325)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (28321)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (28330)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (28318)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (28320)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (28336)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (28339)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (28315)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.56  % (28334)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.57  % (28341)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.57  % (28331)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.57  % (28324)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (28322)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.57  % (28312)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.57  % (28334)Refutation not found, incomplete strategy% (28334)------------------------------
% 0.21/0.57  % (28334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (28334)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (28334)Memory used [KB]: 10746
% 0.21/0.57  % (28334)Time elapsed: 0.123 s
% 0.21/0.57  % (28334)------------------------------
% 0.21/0.57  % (28334)------------------------------
% 0.21/0.58  % (28333)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.58  % (28317)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (28337)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.58  % (28338)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.58  % (28328)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.59  % (28329)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.59  % (28329)Refutation not found, incomplete strategy% (28329)------------------------------
% 0.21/0.59  % (28329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (28329)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (28329)Memory used [KB]: 10618
% 0.21/0.59  % (28329)Time elapsed: 0.176 s
% 0.21/0.59  % (28329)------------------------------
% 0.21/0.59  % (28329)------------------------------
% 0.21/0.60  % (28340)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.78/0.61  % (28319)Refutation found. Thanks to Tanya!
% 1.78/0.61  % SZS status Theorem for theBenchmark
% 1.78/0.61  % SZS output start Proof for theBenchmark
% 1.78/0.61  fof(f1315,plain,(
% 1.78/0.61    $false),
% 1.78/0.61    inference(subsumption_resolution,[],[f1261,f73])).
% 1.78/0.61  fof(f73,plain,(
% 1.78/0.61    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.78/0.61    inference(equality_resolution,[],[f55])).
% 1.78/0.61  fof(f55,plain,(
% 1.78/0.61    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.78/0.61    inference(cnf_transformation,[],[f33])).
% 1.78/0.61  fof(f33,plain,(
% 1.78/0.61    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.78/0.61    inference(flattening,[],[f32])).
% 1.78/0.61  fof(f32,plain,(
% 1.78/0.61    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.78/0.61    inference(nnf_transformation,[],[f9])).
% 1.78/0.61  fof(f9,axiom,(
% 1.78/0.61    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.78/0.61  fof(f1261,plain,(
% 1.78/0.61    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2)),
% 1.78/0.61    inference(backward_demodulation,[],[f41,f1259])).
% 1.78/0.61  fof(f1259,plain,(
% 1.78/0.61    k1_xboole_0 = sK1),
% 1.78/0.61    inference(subsumption_resolution,[],[f1226,f72])).
% 1.78/0.61  fof(f72,plain,(
% 1.78/0.61    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.78/0.61    inference(equality_resolution,[],[f56])).
% 1.78/0.61  fof(f56,plain,(
% 1.78/0.61    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.78/0.61    inference(cnf_transformation,[],[f33])).
% 1.78/0.61  fof(f1226,plain,(
% 1.78/0.61    k1_xboole_0 != k2_zfmisc_1(sK1,k1_xboole_0) | k1_xboole_0 = sK1),
% 1.78/0.61    inference(superposition,[],[f41,f1224])).
% 1.78/0.61  fof(f1224,plain,(
% 1.78/0.61    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.78/0.61    inference(subsumption_resolution,[],[f1218,f1072])).
% 1.78/0.61  fof(f1072,plain,(
% 1.78/0.61    ~r1_tarski(sK1,sK3) | k1_xboole_0 = sK1),
% 1.78/0.61    inference(resolution,[],[f1053,f42])).
% 1.78/0.61  fof(f42,plain,(
% 1.78/0.61    ~r1_tarski(sK2,sK4) | ~r1_tarski(sK1,sK3)),
% 1.78/0.61    inference(cnf_transformation,[],[f25])).
% 1.78/0.61  fof(f25,plain,(
% 1.78/0.61    (~r1_tarski(sK2,sK4) | ~r1_tarski(sK1,sK3)) & k1_xboole_0 != k2_zfmisc_1(sK1,sK2) & r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))),
% 1.78/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f16,f24])).
% 1.78/0.61  fof(f24,plain,(
% 1.78/0.61    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK2,sK4) | ~r1_tarski(sK1,sK3)) & k1_xboole_0 != k2_zfmisc_1(sK1,sK2) & r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))),
% 1.78/0.61    introduced(choice_axiom,[])).
% 1.78/0.61  fof(f16,plain,(
% 1.78/0.61    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.78/0.61    inference(flattening,[],[f15])).
% 1.78/0.61  fof(f15,plain,(
% 1.78/0.61    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.78/0.61    inference(ennf_transformation,[],[f14])).
% 1.78/0.61  fof(f14,negated_conjecture,(
% 1.78/0.61    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.78/0.61    inference(negated_conjecture,[],[f13])).
% 1.78/0.61  fof(f13,conjecture,(
% 1.78/0.61    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 1.78/0.61  fof(f1053,plain,(
% 1.78/0.61    r1_tarski(sK2,sK4) | k1_xboole_0 = sK1),
% 1.78/0.61    inference(superposition,[],[f257,f1016])).
% 1.78/0.61  fof(f1016,plain,(
% 1.78/0.61    sK2 = k3_xboole_0(sK2,sK4) | k1_xboole_0 = sK1),
% 1.78/0.61    inference(resolution,[],[f1004,f160])).
% 1.78/0.61  fof(f160,plain,(
% 1.78/0.61    ( ! [X6,X7] : (~r1_tarski(X6,k3_xboole_0(X6,X7)) | k3_xboole_0(X6,X7) = X6) )),
% 1.78/0.61    inference(resolution,[],[f157,f50])).
% 1.78/0.61  fof(f50,plain,(
% 1.78/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.78/0.61    inference(cnf_transformation,[],[f27])).
% 1.78/0.61  fof(f27,plain,(
% 1.78/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.78/0.61    inference(flattening,[],[f26])).
% 1.78/0.61  fof(f26,plain,(
% 1.78/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.78/0.61    inference(nnf_transformation,[],[f4])).
% 2.00/0.63  fof(f4,axiom,(
% 2.00/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.00/0.63  fof(f157,plain,(
% 2.00/0.63    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.00/0.63    inference(duplicate_literal_removal,[],[f149])).
% 2.00/0.63  fof(f149,plain,(
% 2.00/0.63    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0) | r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.00/0.63    inference(resolution,[],[f139,f53])).
% 2.00/0.63  fof(f53,plain,(
% 2.00/0.63    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.00/0.63    inference(cnf_transformation,[],[f31])).
% 2.00/0.63  fof(f31,plain,(
% 2.00/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.00/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).
% 2.00/0.63  fof(f30,plain,(
% 2.00/0.63    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 2.00/0.63    introduced(choice_axiom,[])).
% 2.00/0.63  fof(f29,plain,(
% 2.00/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.00/0.63    inference(rectify,[],[f28])).
% 2.00/0.63  fof(f28,plain,(
% 2.00/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.00/0.63    inference(nnf_transformation,[],[f19])).
% 2.00/0.63  fof(f19,plain,(
% 2.00/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.00/0.63    inference(ennf_transformation,[],[f2])).
% 2.00/0.63  fof(f2,axiom,(
% 2.00/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.00/0.63  fof(f139,plain,(
% 2.00/0.63    ( ! [X2,X0,X1] : (r2_hidden(sK5(k3_xboole_0(X0,X1),X2),X0) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 2.00/0.63    inference(resolution,[],[f112,f74])).
% 2.00/0.63  fof(f74,plain,(
% 2.00/0.63    ( ! [X0,X1] : (sP0(X1,X0,k3_xboole_0(X0,X1))) )),
% 2.00/0.63    inference(equality_resolution,[],[f65])).
% 2.00/0.63  fof(f65,plain,(
% 2.00/0.63    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.00/0.63    inference(cnf_transformation,[],[f39])).
% 2.00/0.63  fof(f39,plain,(
% 2.00/0.63    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 2.00/0.63    inference(nnf_transformation,[],[f23])).
% 2.00/0.63  fof(f23,plain,(
% 2.00/0.63    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 2.00/0.63    inference(definition_folding,[],[f3,f22])).
% 2.00/0.63  fof(f22,plain,(
% 2.00/0.63    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.00/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.00/0.63  fof(f3,axiom,(
% 2.00/0.63    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.00/0.63  fof(f112,plain,(
% 2.00/0.63    ( ! [X2,X0,X3,X1] : (~sP0(X3,X2,X0) | r2_hidden(sK5(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 2.00/0.63    inference(resolution,[],[f59,f52])).
% 2.00/0.63  fof(f52,plain,(
% 2.00/0.63    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.00/0.63    inference(cnf_transformation,[],[f31])).
% 2.00/0.63  fof(f59,plain,(
% 2.00/0.63    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~sP0(X0,X1,X2)) )),
% 2.00/0.63    inference(cnf_transformation,[],[f38])).
% 2.00/0.63  fof(f38,plain,(
% 2.00/0.63    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 2.00/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).
% 2.00/0.63  fof(f37,plain,(
% 2.00/0.63    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 2.00/0.63    introduced(choice_axiom,[])).
% 2.00/0.63  fof(f36,plain,(
% 2.00/0.63    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 2.00/0.63    inference(rectify,[],[f35])).
% 2.00/0.63  fof(f35,plain,(
% 2.00/0.63    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 2.00/0.63    inference(flattening,[],[f34])).
% 2.00/0.63  fof(f34,plain,(
% 2.00/0.63    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 2.00/0.63    inference(nnf_transformation,[],[f22])).
% 2.00/0.63  fof(f1004,plain,(
% 2.00/0.63    r1_tarski(sK2,k3_xboole_0(sK2,sK4)) | k1_xboole_0 = sK1),
% 2.00/0.63    inference(resolution,[],[f976,f68])).
% 2.00/0.63  fof(f68,plain,(
% 2.00/0.63    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 2.00/0.63    inference(cnf_transformation,[],[f21])).
% 2.00/0.63  fof(f21,plain,(
% 2.00/0.63    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 2.00/0.63    inference(ennf_transformation,[],[f10])).
% 2.00/0.63  fof(f10,axiom,(
% 2.00/0.63    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 2.00/0.63  fof(f976,plain,(
% 2.00/0.63    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,k3_xboole_0(sK2,sK4)))),
% 2.00/0.63    inference(superposition,[],[f426,f89])).
% 2.00/0.63  fof(f89,plain,(
% 2.00/0.63    k2_zfmisc_1(sK1,sK2) = k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))),
% 2.00/0.63    inference(resolution,[],[f47,f40])).
% 2.00/0.63  fof(f40,plain,(
% 2.00/0.63    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))),
% 2.00/0.63    inference(cnf_transformation,[],[f25])).
% 2.00/0.63  fof(f47,plain,(
% 2.00/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.00/0.63    inference(cnf_transformation,[],[f18])).
% 2.00/0.63  fof(f18,plain,(
% 2.00/0.63    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.00/0.63    inference(ennf_transformation,[],[f6])).
% 2.00/0.63  fof(f6,axiom,(
% 2.00/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.00/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.00/0.63  fof(f426,plain,(
% 2.00/0.63    ( ! [X6,X4,X7,X5] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)),k2_zfmisc_1(X4,k3_xboole_0(X6,X7)))) )),
% 2.00/0.63    inference(superposition,[],[f159,f69])).
% 2.09/0.64  fof(f69,plain,(
% 2.09/0.64    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 2.09/0.64    inference(cnf_transformation,[],[f12])).
% 2.09/0.64  fof(f12,axiom,(
% 2.09/0.64    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 2.09/0.64  fof(f159,plain,(
% 2.09/0.64    ( ! [X4,X5,X3] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X3,X4),X5),k2_zfmisc_1(X3,X5))) )),
% 2.09/0.64    inference(resolution,[],[f157,f57])).
% 2.09/0.64  fof(f57,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 2.09/0.64    inference(cnf_transformation,[],[f20])).
% 2.09/0.64  fof(f20,plain,(
% 2.09/0.64    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 2.09/0.64    inference(ennf_transformation,[],[f11])).
% 2.09/0.64  fof(f11,axiom,(
% 2.09/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 2.09/0.64  fof(f257,plain,(
% 2.09/0.64    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 2.09/0.64    inference(duplicate_literal_removal,[],[f247])).
% 2.09/0.64  fof(f247,plain,(
% 2.09/0.64    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1) | r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 2.09/0.64    inference(resolution,[],[f144,f53])).
% 2.09/0.64  fof(f144,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (r2_hidden(sK5(k3_xboole_0(X0,X1),X2),X1) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 2.09/0.64    inference(resolution,[],[f113,f74])).
% 2.09/0.64  fof(f113,plain,(
% 2.09/0.64    ( ! [X2,X0,X3,X1] : (~sP0(X2,X3,X0) | r2_hidden(sK5(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 2.09/0.64    inference(resolution,[],[f60,f52])).
% 2.09/0.64  fof(f60,plain,(
% 2.09/0.64    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~sP0(X0,X1,X2)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f38])).
% 2.09/0.64  fof(f1218,plain,(
% 2.09/0.64    k1_xboole_0 = sK1 | r1_tarski(sK1,sK3) | k1_xboole_0 = sK2),
% 2.09/0.64    inference(resolution,[],[f1033,f67])).
% 2.09/0.64  fof(f67,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 2.09/0.64    inference(cnf_transformation,[],[f21])).
% 2.09/0.64  fof(f1033,plain,(
% 2.09/0.64    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK2)) | k1_xboole_0 = sK1),
% 2.09/0.64    inference(superposition,[],[f929,f1016])).
% 2.09/0.64  fof(f929,plain,(
% 2.09/0.64    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)))),
% 2.09/0.64    inference(superposition,[],[f425,f89])).
% 2.09/0.64  fof(f425,plain,(
% 2.09/0.64    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k2_zfmisc_1(X1,k3_xboole_0(X2,X3)))) )),
% 2.09/0.64    inference(superposition,[],[f259,f69])).
% 2.09/0.64  fof(f259,plain,(
% 2.09/0.64    ( ! [X4,X5,X3] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X3,X4),X5),k2_zfmisc_1(X4,X5))) )),
% 2.09/0.64    inference(resolution,[],[f257,f57])).
% 2.09/0.64  fof(f41,plain,(
% 2.09/0.64    k1_xboole_0 != k2_zfmisc_1(sK1,sK2)),
% 2.09/0.64    inference(cnf_transformation,[],[f25])).
% 2.09/0.64  % SZS output end Proof for theBenchmark
% 2.09/0.64  % (28319)------------------------------
% 2.09/0.64  % (28319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.64  % (28319)Termination reason: Refutation
% 2.09/0.64  
% 2.09/0.64  % (28319)Memory used [KB]: 7291
% 2.09/0.64  % (28319)Time elapsed: 0.201 s
% 2.09/0.64  % (28319)------------------------------
% 2.09/0.64  % (28319)------------------------------
% 2.09/0.64  % (28311)Success in time 0.272 s
%------------------------------------------------------------------------------
