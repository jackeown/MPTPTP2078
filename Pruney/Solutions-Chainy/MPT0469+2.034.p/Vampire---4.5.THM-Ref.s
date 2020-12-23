%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:38 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 613 expanded)
%              Number of leaves         :   30 ( 185 expanded)
%              Depth                    :   20
%              Number of atoms          :  431 (2640 expanded)
%              Number of equality atoms :  126 ( 855 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f696,plain,(
    $false ),
    inference(subsumption_resolution,[],[f695,f631])).

fof(f631,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f577,f80])).

fof(f80,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f577,plain,(
    ! [X4] : ~ r2_hidden(X4,k2_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f557,f561])).

fof(f561,plain,(
    k1_xboole_0 = sK1(k1_xboole_0) ),
    inference(resolution,[],[f546,f80])).

fof(f546,plain,(
    ! [X1] : ~ r2_hidden(X1,sK1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f433,f336])).

fof(f336,plain,(
    ! [X10,X11] :
      ( sK3(k1_xboole_0,X10) = X11
      | ~ r2_hidden(X10,sK1(k1_xboole_0)) ) ),
    inference(resolution,[],[f322,f84])).

fof(f84,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK3(X0,X2),X0)
      | ~ r2_hidden(X2,sK1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X2] :
      ( ( r2_hidden(X2,sK1(X0))
        | ! [X3] :
            ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r2_hidden(X4,X3) )
            | X2 != X3 )
        | ~ r2_hidden(X2,k3_tarski(X0)) )
      & ( ( r2_hidden(sK3(X0,X2),X0)
          & r2_hidden(sK3(X0,X2),sK2(X0,X2))
          & sK2(X0,X2) = X2
          & r2_hidden(X2,k3_tarski(X0)) )
        | ~ r2_hidden(X2,sK1(X0)) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f39,f42,f41,f40])).

% (28737)Termination reason: Refutation not found, incomplete strategy
fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ( r2_hidden(X2,X1)
            | ! [X3] :
                ( ! [X4] :
                    ( ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(X4,X3) )
                | X2 != X3 )
            | ~ r2_hidden(X2,k3_tarski(X0)) )
          & ( ( ? [X5] :
                  ( ? [X6] :
                      ( r2_hidden(X6,X0)
                      & r2_hidden(X6,X5) )
                  & X2 = X5 )
              & r2_hidden(X2,k3_tarski(X0)) )
            | ~ r2_hidden(X2,X1) ) )
     => ! [X2] :
          ( ( r2_hidden(X2,sK1(X0))
            | ! [X3] :
                ( ! [X4] :
                    ( ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(X4,X3) )
                | X2 != X3 )
            | ~ r2_hidden(X2,k3_tarski(X0)) )
          & ( ( ? [X5] :
                  ( ? [X6] :
                      ( r2_hidden(X6,X0)
                      & r2_hidden(X6,X5) )
                  & X2 = X5 )
              & r2_hidden(X2,k3_tarski(X0)) )
            | ~ r2_hidden(X2,sK1(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( r2_hidden(X6,X0)
              & r2_hidden(X6,X5) )
          & X2 = X5 )
     => ( ? [X6] :
            ( r2_hidden(X6,X0)
            & r2_hidden(X6,sK2(X0,X2)) )
        & sK2(X0,X2) = X2 ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X0)
          & r2_hidden(X6,sK2(X0,X2)) )
     => ( r2_hidden(sK3(X0,X2),X0)
        & r2_hidden(sK3(X0,X2),sK2(X0,X2)) ) ) ),
    introduced(choice_axiom,[])).

% (28737)Memory used [KB]: 10746
fof(f39,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ! [X3] :
            ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r2_hidden(X4,X3) )
            | X2 != X3 )
        | ~ r2_hidden(X2,k3_tarski(X0)) )
      & ( ( ? [X5] :
              ( ? [X6] :
                  ( r2_hidden(X6,X0)
                  & r2_hidden(X6,X5) )
              & X2 = X5 )
          & r2_hidden(X2,k3_tarski(X0)) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(rectify,[],[f38])).

% (28737)Time elapsed: 0.134 s
fof(f38,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ! [X3] :
            ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r2_hidden(X4,X3) )
            | X2 != X3 )
        | ~ r2_hidden(X2,k3_tarski(X0)) )
      & ( ( ? [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X4,X3) )
              & X2 = X3 )
          & r2_hidden(X2,k3_tarski(X0)) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(flattening,[],[f37])).

% (28737)------------------------------
% (28737)------------------------------
fof(f37,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ! [X3] :
            ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r2_hidden(X4,X3) )
            | X2 != X3 )
        | ~ r2_hidden(X2,k3_tarski(X0)) )
      & ( ( ? [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X4,X3) )
              & X2 = X3 )
          & r2_hidden(X2,k3_tarski(X0)) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( r2_hidden(X2,X1)
    <=> ( ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X4,X3) )
            & X2 = X3 )
        & r2_hidden(X2,k3_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e1_138_1__zfmisc_1)).

fof(f322,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | X0 = X1 ) ),
    inference(subsumption_resolution,[],[f321,f157])).

fof(f157,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f142,f156])).

fof(f156,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f155,f76])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f155,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f89,f86])).

fof(f86,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f89,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f142,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f321,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(X0,k1_xboole_0)
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(resolution,[],[f300,f79])).

fof(f79,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).

fof(f300,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_xboole_0(X3,k1_tarski(X4))
      | X2 = X4
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f242,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f242,plain,(
    ! [X8,X7,X9] :
      ( ~ r1_tarski(X8,k1_tarski(X9))
      | ~ r2_hidden(X7,X8)
      | X7 = X9 ) ),
    inference(resolution,[],[f223,f141])).

fof(f141,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK15(X0,X1) != X0
            | ~ r2_hidden(sK15(X0,X1),X1) )
          & ( sK15(X0,X1) = X0
            | r2_hidden(sK15(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f71,f72])).

fof(f72,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK15(X0,X1) != X0
          | ~ r2_hidden(sK15(X0,X1),X1) )
        & ( sK15(X0,X1) = X0
          | r2_hidden(sK15(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
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
    inference(rectify,[],[f70])).

fof(f70,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f223,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2)
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f181,f130])).

fof(f130,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK5(X0,X1),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r1_tarski(sK5(X0,X1),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f49,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK5(X0,X1),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( r1_tarski(sK5(X0,X1),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(superposition,[],[f136,f77])).

fof(f77,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f136,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK12(X0,X1),X3) )
            | ~ r2_hidden(sK12(X0,X1),X1) )
          & ( ( r2_hidden(sK13(X0,X1),X0)
              & r2_hidden(sK12(X0,X1),sK13(X0,X1)) )
            | r2_hidden(sK12(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK14(X0,X5),X0)
                & r2_hidden(X5,sK14(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14])],[f65,f68,f67,f66])).

fof(f66,plain,(
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
              | ~ r2_hidden(sK12(X0,X1),X3) )
          | ~ r2_hidden(sK12(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK12(X0,X1),X4) )
          | r2_hidden(sK12(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK12(X0,X1),X4) )
     => ( r2_hidden(sK13(X0,X1),X0)
        & r2_hidden(sK12(X0,X1),sK13(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK14(X0,X5),X0)
        & r2_hidden(X5,sK14(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
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
    inference(rectify,[],[f64])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f433,plain,(
    ! [X1] :
      ( k1_xboole_0 != sK3(k1_xboole_0,X1)
      | ~ r2_hidden(X1,sK1(k1_xboole_0)) ) ),
    inference(superposition,[],[f157,f336])).

fof(f557,plain,(
    ! [X4] : ~ r2_hidden(X4,k2_relat_1(sK1(k1_xboole_0))) ),
    inference(resolution,[],[f546,f133])).

fof(f133,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f53,f56,f55,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f695,plain,(
    k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f685])).

fof(f685,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f75,f676])).

fof(f676,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f580,f80])).

fof(f580,plain,(
    ! [X7] : ~ r2_hidden(X7,k1_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f560,f561])).

fof(f560,plain,(
    ! [X7] : ~ r2_hidden(X7,k1_relat_1(sK1(k1_xboole_0))) ),
    inference(resolution,[],[f546,f135])).

fof(f135,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK11(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK11(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK9(X0,X1),X3),X0)
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0)
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK11(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f59,f62,f61,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK9(X0,X1),X3),X0)
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK9(X0,X1),X4),X0)
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK9(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK11(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f75,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (28727)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.50  % (28732)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (28740)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (28730)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (28744)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.51  % (28727)Refutation not found, incomplete strategy% (28727)------------------------------
% 0.20/0.51  % (28727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (28727)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (28727)Memory used [KB]: 1663
% 0.20/0.51  % (28727)Time elapsed: 0.092 s
% 0.20/0.51  % (28727)------------------------------
% 0.20/0.51  % (28727)------------------------------
% 0.20/0.51  % (28731)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (28736)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (28748)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.23/0.52  % (28742)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.23/0.52  % (28750)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.23/0.52  % (28728)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.23/0.52  % (28744)Refutation not found, incomplete strategy% (28744)------------------------------
% 1.23/0.52  % (28744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (28744)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.52  
% 1.23/0.52  % (28744)Memory used [KB]: 1791
% 1.23/0.52  % (28744)Time elapsed: 0.108 s
% 1.23/0.52  % (28744)------------------------------
% 1.23/0.52  % (28744)------------------------------
% 1.23/0.52  % (28749)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.23/0.52  % (28737)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.23/0.52  % (28734)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.23/0.53  % (28741)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.23/0.53  % (28747)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.23/0.53  % (28729)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.23/0.53  % (28726)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.33/0.53  % (28735)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.33/0.53  % (28741)Refutation not found, incomplete strategy% (28741)------------------------------
% 1.33/0.53  % (28741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (28741)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (28741)Memory used [KB]: 1791
% 1.33/0.53  % (28741)Time elapsed: 0.129 s
% 1.33/0.53  % (28741)------------------------------
% 1.33/0.53  % (28741)------------------------------
% 1.33/0.54  % (28745)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.33/0.54  % (28756)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.33/0.54  % (28752)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.33/0.54  % (28739)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.33/0.54  % (28745)Refutation not found, incomplete strategy% (28745)------------------------------
% 1.33/0.54  % (28745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (28746)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.33/0.54  % (28737)Refutation not found, incomplete strategy% (28737)------------------------------
% 1.33/0.54  % (28737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (28745)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (28745)Memory used [KB]: 1663
% 1.33/0.54  % (28745)Time elapsed: 0.130 s
% 1.33/0.54  % (28745)------------------------------
% 1.33/0.54  % (28745)------------------------------
% 1.33/0.54  % (28736)Refutation found. Thanks to Tanya!
% 1.33/0.54  % SZS status Theorem for theBenchmark
% 1.33/0.54  % SZS output start Proof for theBenchmark
% 1.33/0.54  fof(f696,plain,(
% 1.33/0.54    $false),
% 1.33/0.54    inference(subsumption_resolution,[],[f695,f631])).
% 1.33/0.54  fof(f631,plain,(
% 1.33/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.33/0.54    inference(resolution,[],[f577,f80])).
% 1.33/0.54  fof(f80,plain,(
% 1.33/0.54    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 1.33/0.54    inference(cnf_transformation,[],[f36])).
% 1.33/0.54  fof(f36,plain,(
% 1.33/0.54    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 1.33/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f35])).
% 1.33/0.54  fof(f35,plain,(
% 1.33/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f31,plain,(
% 1.33/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.33/0.54    inference(ennf_transformation,[],[f3])).
% 1.33/0.54  fof(f3,axiom,(
% 1.33/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.33/0.54  fof(f577,plain,(
% 1.33/0.54    ( ! [X4] : (~r2_hidden(X4,k2_relat_1(k1_xboole_0))) )),
% 1.33/0.54    inference(backward_demodulation,[],[f557,f561])).
% 1.33/0.54  fof(f561,plain,(
% 1.33/0.54    k1_xboole_0 = sK1(k1_xboole_0)),
% 1.33/0.54    inference(resolution,[],[f546,f80])).
% 1.33/0.54  fof(f546,plain,(
% 1.33/0.54    ( ! [X1] : (~r2_hidden(X1,sK1(k1_xboole_0))) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f433,f336])).
% 1.33/0.54  fof(f336,plain,(
% 1.33/0.54    ( ! [X10,X11] : (sK3(k1_xboole_0,X10) = X11 | ~r2_hidden(X10,sK1(k1_xboole_0))) )),
% 1.33/0.54    inference(resolution,[],[f322,f84])).
% 1.33/0.54  fof(f84,plain,(
% 1.33/0.54    ( ! [X2,X0] : (r2_hidden(sK3(X0,X2),X0) | ~r2_hidden(X2,sK1(X0))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f43])).
% 1.33/0.54  fof(f43,plain,(
% 1.33/0.54    ! [X0] : ! [X2] : ((r2_hidden(X2,sK1(X0)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X0) | ~r2_hidden(X4,X3)) | X2 != X3) | ~r2_hidden(X2,k3_tarski(X0))) & ((((r2_hidden(sK3(X0,X2),X0) & r2_hidden(sK3(X0,X2),sK2(X0,X2))) & sK2(X0,X2) = X2) & r2_hidden(X2,k3_tarski(X0))) | ~r2_hidden(X2,sK1(X0))))),
% 1.33/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f39,f42,f41,f40])).
% 1.33/0.54  % (28737)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  fof(f40,plain,(
% 1.33/0.54    ! [X0] : (? [X1] : ! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (! [X4] : (~r2_hidden(X4,X0) | ~r2_hidden(X4,X3)) | X2 != X3) | ~r2_hidden(X2,k3_tarski(X0))) & ((? [X5] : (? [X6] : (r2_hidden(X6,X0) & r2_hidden(X6,X5)) & X2 = X5) & r2_hidden(X2,k3_tarski(X0))) | ~r2_hidden(X2,X1))) => ! [X2] : ((r2_hidden(X2,sK1(X0)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X0) | ~r2_hidden(X4,X3)) | X2 != X3) | ~r2_hidden(X2,k3_tarski(X0))) & ((? [X5] : (? [X6] : (r2_hidden(X6,X0) & r2_hidden(X6,X5)) & X2 = X5) & r2_hidden(X2,k3_tarski(X0))) | ~r2_hidden(X2,sK1(X0)))))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  
% 1.33/0.54  fof(f41,plain,(
% 1.33/0.54    ! [X2,X0] : (? [X5] : (? [X6] : (r2_hidden(X6,X0) & r2_hidden(X6,X5)) & X2 = X5) => (? [X6] : (r2_hidden(X6,X0) & r2_hidden(X6,sK2(X0,X2))) & sK2(X0,X2) = X2))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f42,plain,(
% 1.33/0.54    ! [X2,X0] : (? [X6] : (r2_hidden(X6,X0) & r2_hidden(X6,sK2(X0,X2))) => (r2_hidden(sK3(X0,X2),X0) & r2_hidden(sK3(X0,X2),sK2(X0,X2))))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  % (28737)Memory used [KB]: 10746
% 1.33/0.54  fof(f39,plain,(
% 1.33/0.54    ! [X0] : ? [X1] : ! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (! [X4] : (~r2_hidden(X4,X0) | ~r2_hidden(X4,X3)) | X2 != X3) | ~r2_hidden(X2,k3_tarski(X0))) & ((? [X5] : (? [X6] : (r2_hidden(X6,X0) & r2_hidden(X6,X5)) & X2 = X5) & r2_hidden(X2,k3_tarski(X0))) | ~r2_hidden(X2,X1)))),
% 1.33/0.54    inference(rectify,[],[f38])).
% 1.33/0.54  % (28737)Time elapsed: 0.134 s
% 1.33/0.54  fof(f38,plain,(
% 1.33/0.54    ! [X0] : ? [X1] : ! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (! [X4] : (~r2_hidden(X4,X0) | ~r2_hidden(X4,X3)) | X2 != X3) | ~r2_hidden(X2,k3_tarski(X0))) & ((? [X3] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X4,X3)) & X2 = X3) & r2_hidden(X2,k3_tarski(X0))) | ~r2_hidden(X2,X1)))),
% 1.33/0.54    inference(flattening,[],[f37])).
% 1.33/0.54  % (28737)------------------------------
% 1.33/0.54  % (28737)------------------------------
% 1.33/0.54  fof(f37,plain,(
% 1.33/0.54    ! [X0] : ? [X1] : ! [X2] : ((r2_hidden(X2,X1) | (! [X3] : (! [X4] : (~r2_hidden(X4,X0) | ~r2_hidden(X4,X3)) | X2 != X3) | ~r2_hidden(X2,k3_tarski(X0)))) & ((? [X3] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X4,X3)) & X2 = X3) & r2_hidden(X2,k3_tarski(X0))) | ~r2_hidden(X2,X1)))),
% 1.33/0.54    inference(nnf_transformation,[],[f18])).
% 1.33/0.54  fof(f18,axiom,(
% 1.33/0.54    ! [X0] : ? [X1] : ! [X2] : (r2_hidden(X2,X1) <=> (? [X3] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X4,X3)) & X2 = X3) & r2_hidden(X2,k3_tarski(X0))))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e1_138_1__zfmisc_1)).
% 1.33/0.54  fof(f322,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | X0 = X1) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f321,f157])).
% 1.33/0.54  fof(f157,plain,(
% 1.33/0.54    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 1.33/0.54    inference(backward_demodulation,[],[f142,f156])).
% 1.33/0.54  fof(f156,plain,(
% 1.33/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.33/0.54    inference(forward_demodulation,[],[f155,f76])).
% 1.33/0.54  fof(f76,plain,(
% 1.33/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f7])).
% 1.33/0.54  fof(f7,axiom,(
% 1.33/0.54    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.33/0.54  fof(f155,plain,(
% 1.33/0.54    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 1.33/0.54    inference(superposition,[],[f89,f86])).
% 1.33/0.54  fof(f86,plain,(
% 1.33/0.54    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.33/0.54    inference(cnf_transformation,[],[f27])).
% 1.33/0.54  fof(f27,plain,(
% 1.33/0.54    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.33/0.54    inference(rectify,[],[f2])).
% 1.33/0.54  fof(f2,axiom,(
% 1.33/0.54    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.33/0.54  fof(f89,plain,(
% 1.33/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f5])).
% 1.33/0.54  fof(f5,axiom,(
% 1.33/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.33/0.54  fof(f142,plain,(
% 1.33/0.54    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 1.33/0.54    inference(equality_resolution,[],[f119])).
% 1.33/0.54  fof(f119,plain,(
% 1.33/0.54    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f74])).
% 1.33/0.54  fof(f74,plain,(
% 1.33/0.54    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.33/0.54    inference(nnf_transformation,[],[f19])).
% 1.33/0.54  fof(f19,axiom,(
% 1.33/0.54    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.33/0.54  fof(f321,plain,(
% 1.33/0.54    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(X0,k1_xboole_0) | k1_xboole_0 = k1_tarski(X1)) )),
% 1.33/0.54    inference(resolution,[],[f300,f79])).
% 1.33/0.54  fof(f79,plain,(
% 1.33/0.54    ( ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 1.33/0.54    inference(cnf_transformation,[],[f30])).
% 1.33/0.54  fof(f30,plain,(
% 1.33/0.54    ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0)),
% 1.33/0.54    inference(ennf_transformation,[],[f6])).
% 1.33/0.54  fof(f6,axiom,(
% 1.33/0.54    ! [X0] : (k1_xboole_0 != X0 => r2_xboole_0(k1_xboole_0,X0))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).
% 1.33/0.54  fof(f300,plain,(
% 1.33/0.54    ( ! [X4,X2,X3] : (~r2_xboole_0(X3,k1_tarski(X4)) | X2 = X4 | ~r2_hidden(X2,X3)) )),
% 1.33/0.54    inference(resolution,[],[f242,f95])).
% 1.33/0.54  fof(f95,plain,(
% 1.33/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f34])).
% 1.33/0.54  fof(f34,plain,(
% 1.33/0.54    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1))),
% 1.33/0.54    inference(ennf_transformation,[],[f28])).
% 1.33/0.54  fof(f28,plain,(
% 1.33/0.54    ! [X0,X1] : (r2_xboole_0(X0,X1) => (X0 != X1 & r1_tarski(X0,X1)))),
% 1.33/0.54    inference(unused_predicate_definition_removal,[],[f1])).
% 1.33/0.54  fof(f1,axiom,(
% 1.33/0.54    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.33/0.54  fof(f242,plain,(
% 1.33/0.54    ( ! [X8,X7,X9] : (~r1_tarski(X8,k1_tarski(X9)) | ~r2_hidden(X7,X8) | X7 = X9) )),
% 1.33/0.54    inference(resolution,[],[f223,f141])).
% 1.33/0.54  fof(f141,plain,(
% 1.33/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.33/0.54    inference(equality_resolution,[],[f115])).
% 1.33/0.54  fof(f115,plain,(
% 1.33/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.33/0.54    inference(cnf_transformation,[],[f73])).
% 1.33/0.54  fof(f73,plain,(
% 1.33/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK15(X0,X1) != X0 | ~r2_hidden(sK15(X0,X1),X1)) & (sK15(X0,X1) = X0 | r2_hidden(sK15(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.33/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f71,f72])).
% 1.33/0.54  fof(f72,plain,(
% 1.33/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK15(X0,X1) != X0 | ~r2_hidden(sK15(X0,X1),X1)) & (sK15(X0,X1) = X0 | r2_hidden(sK15(X0,X1),X1))))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f71,plain,(
% 1.33/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.33/0.54    inference(rectify,[],[f70])).
% 1.33/0.54  fof(f70,plain,(
% 1.33/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.33/0.54    inference(nnf_transformation,[],[f8])).
% 1.33/0.54  fof(f8,axiom,(
% 1.33/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.33/0.54  fof(f223,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,X2) | ~r1_tarski(X2,X1)) )),
% 1.33/0.54    inference(resolution,[],[f181,f130])).
% 1.33/0.54  fof(f130,plain,(
% 1.33/0.54    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.33/0.54    inference(equality_resolution,[],[f98])).
% 1.33/0.54  fof(f98,plain,(
% 1.33/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.33/0.54    inference(cnf_transformation,[],[f51])).
% 1.33/0.54  fof(f51,plain,(
% 1.33/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.33/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f49,f50])).
% 1.33/0.54  fof(f50,plain,(
% 1.33/0.54    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f49,plain,(
% 1.33/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.33/0.54    inference(rectify,[],[f48])).
% 1.33/0.54  fof(f48,plain,(
% 1.33/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.33/0.54    inference(nnf_transformation,[],[f16])).
% 1.33/0.54  fof(f16,axiom,(
% 1.33/0.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.33/0.54  fof(f181,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 1.33/0.54    inference(superposition,[],[f136,f77])).
% 1.33/0.54  fof(f77,plain,(
% 1.33/0.54    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 1.33/0.54    inference(cnf_transformation,[],[f20])).
% 1.33/0.54  fof(f20,axiom,(
% 1.33/0.54    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 1.33/0.54  fof(f136,plain,(
% 1.33/0.54    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 1.33/0.54    inference(equality_resolution,[],[f111])).
% 1.33/0.54  fof(f111,plain,(
% 1.33/0.54    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 1.33/0.54    inference(cnf_transformation,[],[f69])).
% 1.33/0.54  fof(f69,plain,(
% 1.33/0.54    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK12(X0,X1),X3)) | ~r2_hidden(sK12(X0,X1),X1)) & ((r2_hidden(sK13(X0,X1),X0) & r2_hidden(sK12(X0,X1),sK13(X0,X1))) | r2_hidden(sK12(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK14(X0,X5),X0) & r2_hidden(X5,sK14(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 1.33/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14])],[f65,f68,f67,f66])).
% 1.33/0.54  fof(f66,plain,(
% 1.33/0.54    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK12(X0,X1),X3)) | ~r2_hidden(sK12(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK12(X0,X1),X4)) | r2_hidden(sK12(X0,X1),X1))))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f67,plain,(
% 1.33/0.54    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK12(X0,X1),X4)) => (r2_hidden(sK13(X0,X1),X0) & r2_hidden(sK12(X0,X1),sK13(X0,X1))))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f68,plain,(
% 1.33/0.54    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK14(X0,X5),X0) & r2_hidden(X5,sK14(X0,X5))))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f65,plain,(
% 1.33/0.54    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 1.33/0.54    inference(rectify,[],[f64])).
% 1.33/0.54  fof(f64,plain,(
% 1.33/0.54    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 1.33/0.54    inference(nnf_transformation,[],[f17])).
% 1.33/0.54  fof(f17,axiom,(
% 1.33/0.54    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 1.33/0.54  fof(f433,plain,(
% 1.33/0.54    ( ! [X1] : (k1_xboole_0 != sK3(k1_xboole_0,X1) | ~r2_hidden(X1,sK1(k1_xboole_0))) )),
% 1.33/0.54    inference(superposition,[],[f157,f336])).
% 1.33/0.54  fof(f557,plain,(
% 1.33/0.54    ( ! [X4] : (~r2_hidden(X4,k2_relat_1(sK1(k1_xboole_0)))) )),
% 1.33/0.54    inference(resolution,[],[f546,f133])).
% 1.33/0.54  fof(f133,plain,(
% 1.33/0.54    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 1.33/0.54    inference(equality_resolution,[],[f101])).
% 1.33/0.54  fof(f101,plain,(
% 1.33/0.54    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 1.33/0.54    inference(cnf_transformation,[],[f57])).
% 1.33/0.54  fof(f57,plain,(
% 1.33/0.54    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.33/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f53,f56,f55,f54])).
% 1.33/0.54  fof(f54,plain,(
% 1.33/0.54    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f55,plain,(
% 1.33/0.54    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f56,plain,(
% 1.33/0.54    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f53,plain,(
% 1.33/0.54    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.33/0.54    inference(rectify,[],[f52])).
% 1.33/0.54  fof(f52,plain,(
% 1.33/0.54    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.33/0.54    inference(nnf_transformation,[],[f24])).
% 1.33/0.54  fof(f24,axiom,(
% 1.33/0.54    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.33/0.54  fof(f695,plain,(
% 1.33/0.54    k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 1.33/0.54    inference(trivial_inequality_removal,[],[f685])).
% 1.33/0.54  fof(f685,plain,(
% 1.33/0.54    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 1.33/0.54    inference(backward_demodulation,[],[f75,f676])).
% 1.33/0.54  fof(f676,plain,(
% 1.33/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.33/0.54    inference(resolution,[],[f580,f80])).
% 1.33/0.54  fof(f580,plain,(
% 1.33/0.54    ( ! [X7] : (~r2_hidden(X7,k1_relat_1(k1_xboole_0))) )),
% 1.33/0.54    inference(backward_demodulation,[],[f560,f561])).
% 1.33/0.54  fof(f560,plain,(
% 1.33/0.54    ( ! [X7] : (~r2_hidden(X7,k1_relat_1(sK1(k1_xboole_0)))) )),
% 1.33/0.54    inference(resolution,[],[f546,f135])).
% 1.33/0.54  fof(f135,plain,(
% 1.33/0.54    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK11(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 1.33/0.54    inference(equality_resolution,[],[f105])).
% 1.33/0.54  fof(f105,plain,(
% 1.33/0.54    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK11(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 1.33/0.54    inference(cnf_transformation,[],[f63])).
% 1.33/0.54  fof(f63,plain,(
% 1.33/0.54    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK9(X0,X1),X3),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0) | r2_hidden(sK9(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK11(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.33/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f59,f62,f61,f60])).
% 1.33/0.54  fof(f60,plain,(
% 1.33/0.54    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK9(X0,X1),X3),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK9(X0,X1),X4),X0) | r2_hidden(sK9(X0,X1),X1))))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f61,plain,(
% 1.33/0.54    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK9(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X0))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f62,plain,(
% 1.33/0.54    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK11(X0,X5)),X0))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f59,plain,(
% 1.33/0.54    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.33/0.54    inference(rectify,[],[f58])).
% 1.33/0.54  fof(f58,plain,(
% 1.33/0.54    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.33/0.54    inference(nnf_transformation,[],[f23])).
% 1.33/0.54  fof(f23,axiom,(
% 1.33/0.54    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 1.33/0.54  fof(f75,plain,(
% 1.33/0.54    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.33/0.54    inference(cnf_transformation,[],[f29])).
% 1.33/0.54  fof(f29,plain,(
% 1.33/0.54    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.33/0.54    inference(ennf_transformation,[],[f26])).
% 1.33/0.54  fof(f26,negated_conjecture,(
% 1.33/0.54    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 1.33/0.54    inference(negated_conjecture,[],[f25])).
% 1.33/0.54  fof(f25,conjecture,(
% 1.33/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.33/0.54  % SZS output end Proof for theBenchmark
% 1.33/0.54  % (28736)------------------------------
% 1.33/0.54  % (28736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (28736)Termination reason: Refutation
% 1.33/0.54  
% 1.33/0.54  % (28736)Memory used [KB]: 2302
% 1.33/0.54  % (28736)Time elapsed: 0.123 s
% 1.33/0.54  % (28736)------------------------------
% 1.33/0.54  % (28736)------------------------------
% 1.33/0.54  % (28722)Success in time 0.182 s
%------------------------------------------------------------------------------
