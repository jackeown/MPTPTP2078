%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:24 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 363 expanded)
%              Number of leaves         :   10 ( 114 expanded)
%              Depth                    :   18
%              Number of atoms          :  228 ( 756 expanded)
%              Number of equality atoms :  158 ( 553 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(subsumption_resolution,[],[f275,f121])).

fof(f121,plain,(
    sK1 != k1_mcart_1(sK0) ),
    inference(subsumption_resolution,[],[f24,f116])).

fof(f116,plain,(
    sK3 = k2_mcart_1(sK0) ),
    inference(resolution,[],[f103,f45])).

fof(f45,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f23,f43,f44])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f43])).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( sK3 != k2_mcart_1(sK0)
      | ( sK2 != k1_mcart_1(sK0)
        & sK1 != k1_mcart_1(sK0) ) )
    & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( k2_mcart_1(X0) != X3
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) )
   => ( ( sK3 != k2_mcart_1(sK0)
        | ( sK2 != k1_mcart_1(sK0)
          & sK1 != k1_mcart_1(sK0) ) )
      & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k2_mcart_1(X0) != X3
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
       => ( k2_mcart_1(X0) = X3
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
     => ( k2_mcart_1(X0) = X3
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

fof(f103,plain,(
    ! [X12,X13,X11] :
      ( ~ r2_hidden(X12,k2_zfmisc_1(X13,k2_enumset1(X11,X11,X11,X11)))
      | k2_mcart_1(X12) = X11 ) ),
    inference(superposition,[],[f67,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f41,f44,f43,f44])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_zfmisc_1)).

fof(f67,plain,(
    ! [X4,X5,X3] : ~ r2_hidden(X3,k2_zfmisc_1(X4,k4_xboole_0(X5,k2_enumset1(k2_mcart_1(X3),k2_mcart_1(X3),k2_mcart_1(X3),k2_mcart_1(X3))))) ),
    inference(resolution,[],[f65,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f65,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f39,f44])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f24,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f275,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(resolution,[],[f272,f102])).

fof(f102,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(X9,k2_zfmisc_1(k2_enumset1(X8,X8,X8,X8),X10))
      | k1_mcart_1(X9) = X8 ) ),
    inference(superposition,[],[f66,f57])).

fof(f66,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(k4_xboole_0(X1,k2_enumset1(k1_mcart_1(X0),k1_mcart_1(X0),k1_mcart_1(X0),k1_mcart_1(X0))),X2)) ),
    inference(resolution,[],[f65,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f272,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(backward_demodulation,[],[f45,f270])).

fof(f270,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f269,f121])).

fof(f269,plain,
    ( sK1 = k1_mcart_1(sK0)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f264,f122])).

fof(f122,plain,(
    sK2 != k1_mcart_1(sK0) ),
    inference(subsumption_resolution,[],[f25,f116])).

fof(f25,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f264,plain,
    ( sK2 = k1_mcart_1(sK0)
    | sK1 = k1_mcart_1(sK0)
    | sK1 = sK2 ),
    inference(resolution,[],[f195,f45])).

fof(f195,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r2_hidden(X8,k2_zfmisc_1(k2_enumset1(X6,X6,X6,X7),X9))
      | k1_mcart_1(X8) = X7
      | k1_mcart_1(X8) = X6
      | X6 = X7 ) ),
    inference(resolution,[],[f182,f26])).

fof(f182,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X2,X2,X2,X4))
      | X2 = X4
      | X3 = X4
      | X2 = X3 ) ),
    inference(resolution,[],[f104,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f44])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X1,X1,X1,X1)))
      | X0 = X2
      | X0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X1,X1,X1,X1)))
      | X0 = X2
      | X0 = X2
      | X0 = X2
      | X0 = X1 ) ),
    inference(superposition,[],[f64,f57])).

fof(f64,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f28,f42])).

fof(f28,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).

fof(f19,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:38:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.54  % (27954)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.57  % (27972)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.57  % (27959)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.57  % (27959)Refutation not found, incomplete strategy% (27959)------------------------------
% 0.20/0.57  % (27959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (27959)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (27959)Memory used [KB]: 10618
% 0.20/0.57  % (27959)Time elapsed: 0.133 s
% 0.20/0.57  % (27959)------------------------------
% 0.20/0.57  % (27959)------------------------------
% 0.20/0.57  % (27971)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.57  % (27964)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.61/0.57  % (27956)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.61/0.57  % (27963)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.61/0.57  % (27953)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.61/0.58  % (27975)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.61/0.58  % (27954)Refutation found. Thanks to Tanya!
% 1.61/0.58  % SZS status Theorem for theBenchmark
% 1.61/0.58  % SZS output start Proof for theBenchmark
% 1.61/0.58  fof(f279,plain,(
% 1.61/0.58    $false),
% 1.61/0.58    inference(subsumption_resolution,[],[f275,f121])).
% 1.61/0.58  fof(f121,plain,(
% 1.61/0.58    sK1 != k1_mcart_1(sK0)),
% 1.61/0.58    inference(subsumption_resolution,[],[f24,f116])).
% 1.61/0.58  fof(f116,plain,(
% 1.61/0.58    sK3 = k2_mcart_1(sK0)),
% 1.61/0.58    inference(resolution,[],[f103,f45])).
% 1.61/0.58  fof(f45,plain,(
% 1.61/0.58    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK3,sK3,sK3,sK3)))),
% 1.61/0.58    inference(definition_unfolding,[],[f23,f43,f44])).
% 1.61/0.58  fof(f44,plain,(
% 1.61/0.58    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.61/0.58    inference(definition_unfolding,[],[f37,f43])).
% 1.61/0.58  fof(f37,plain,(
% 1.61/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f2])).
% 1.61/0.58  fof(f2,axiom,(
% 1.61/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.61/0.58  fof(f43,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.61/0.58    inference(definition_unfolding,[],[f36,f42])).
% 1.61/0.58  fof(f42,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f4])).
% 1.61/0.58  fof(f4,axiom,(
% 1.61/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.61/0.58  fof(f36,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f3])).
% 1.61/0.58  fof(f3,axiom,(
% 1.61/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.61/0.58  fof(f23,plain,(
% 1.61/0.58    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3)))),
% 1.61/0.58    inference(cnf_transformation,[],[f15])).
% 1.61/0.58  fof(f15,plain,(
% 1.61/0.58    (sK3 != k2_mcart_1(sK0) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3)))),
% 1.61/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f14])).
% 1.61/0.58  fof(f14,plain,(
% 1.61/0.58    ? [X0,X1,X2,X3] : ((k2_mcart_1(X0) != X3 | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))) => ((sK3 != k2_mcart_1(sK0) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))))),
% 1.61/0.58    introduced(choice_axiom,[])).
% 1.61/0.58  fof(f10,plain,(
% 1.61/0.58    ? [X0,X1,X2,X3] : ((k2_mcart_1(X0) != X3 | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))))),
% 1.61/0.58    inference(ennf_transformation,[],[f9])).
% 1.61/0.58  fof(f9,negated_conjecture,(
% 1.61/0.58    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) => (k2_mcart_1(X0) = X3 & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 1.61/0.58    inference(negated_conjecture,[],[f8])).
% 1.61/0.58  fof(f8,conjecture,(
% 1.61/0.58    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) => (k2_mcart_1(X0) = X3 & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).
% 1.61/0.58  fof(f103,plain,(
% 1.61/0.58    ( ! [X12,X13,X11] : (~r2_hidden(X12,k2_zfmisc_1(X13,k2_enumset1(X11,X11,X11,X11))) | k2_mcart_1(X12) = X11) )),
% 1.61/0.58    inference(superposition,[],[f67,f57])).
% 1.61/0.58  fof(f57,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X1,X1,X1,X1)) | X0 = X1) )),
% 1.61/0.58    inference(definition_unfolding,[],[f41,f44,f43,f44])).
% 1.61/0.58  fof(f41,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) | X0 = X1) )),
% 1.61/0.58    inference(cnf_transformation,[],[f13])).
% 1.61/0.58  fof(f13,plain,(
% 1.61/0.58    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) | X0 = X1)),
% 1.61/0.58    inference(ennf_transformation,[],[f5])).
% 1.61/0.58  fof(f5,axiom,(
% 1.61/0.58    ! [X0,X1] : (X0 != X1 => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)))),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_zfmisc_1)).
% 1.61/0.58  fof(f67,plain,(
% 1.61/0.58    ( ! [X4,X5,X3] : (~r2_hidden(X3,k2_zfmisc_1(X4,k4_xboole_0(X5,k2_enumset1(k2_mcart_1(X3),k2_mcart_1(X3),k2_mcart_1(X3),k2_mcart_1(X3)))))) )),
% 1.61/0.58    inference(resolution,[],[f65,f27])).
% 1.61/0.58  fof(f27,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f11])).
% 1.61/0.58  fof(f11,plain,(
% 1.61/0.58    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.61/0.58    inference(ennf_transformation,[],[f7])).
% 1.61/0.58  fof(f7,axiom,(
% 1.61/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.61/0.58  fof(f65,plain,(
% 1.61/0.58    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 1.61/0.58    inference(equality_resolution,[],[f55])).
% 1.61/0.58  fof(f55,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 1.61/0.58    inference(definition_unfolding,[],[f39,f44])).
% 1.61/0.58  fof(f39,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f22])).
% 1.61/0.58  fof(f22,plain,(
% 1.61/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.61/0.58    inference(flattening,[],[f21])).
% 1.61/0.58  fof(f21,plain,(
% 1.61/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.61/0.58    inference(nnf_transformation,[],[f6])).
% 1.61/0.58  fof(f6,axiom,(
% 1.61/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.61/0.58  fof(f24,plain,(
% 1.61/0.58    sK3 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 1.61/0.58    inference(cnf_transformation,[],[f15])).
% 1.61/0.58  fof(f275,plain,(
% 1.61/0.58    sK1 = k1_mcart_1(sK0)),
% 1.61/0.58    inference(resolution,[],[f272,f102])).
% 1.61/0.58  fof(f102,plain,(
% 1.61/0.58    ( ! [X10,X8,X9] : (~r2_hidden(X9,k2_zfmisc_1(k2_enumset1(X8,X8,X8,X8),X10)) | k1_mcart_1(X9) = X8) )),
% 1.61/0.58    inference(superposition,[],[f66,f57])).
% 1.61/0.58  fof(f66,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k4_xboole_0(X1,k2_enumset1(k1_mcart_1(X0),k1_mcart_1(X0),k1_mcart_1(X0),k1_mcart_1(X0))),X2))) )),
% 1.61/0.58    inference(resolution,[],[f65,f26])).
% 1.61/0.58  fof(f26,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f11])).
% 1.61/0.58  fof(f272,plain,(
% 1.61/0.58    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK3,sK3,sK3,sK3)))),
% 1.61/0.58    inference(backward_demodulation,[],[f45,f270])).
% 1.61/0.58  fof(f270,plain,(
% 1.61/0.58    sK1 = sK2),
% 1.61/0.58    inference(subsumption_resolution,[],[f269,f121])).
% 1.61/0.58  fof(f269,plain,(
% 1.61/0.58    sK1 = k1_mcart_1(sK0) | sK1 = sK2),
% 1.61/0.58    inference(subsumption_resolution,[],[f264,f122])).
% 1.61/0.58  fof(f122,plain,(
% 1.61/0.58    sK2 != k1_mcart_1(sK0)),
% 1.61/0.58    inference(subsumption_resolution,[],[f25,f116])).
% 1.61/0.58  fof(f25,plain,(
% 1.61/0.58    sK3 != k2_mcart_1(sK0) | sK2 != k1_mcart_1(sK0)),
% 1.61/0.58    inference(cnf_transformation,[],[f15])).
% 1.61/0.58  fof(f264,plain,(
% 1.61/0.58    sK2 = k1_mcart_1(sK0) | sK1 = k1_mcart_1(sK0) | sK1 = sK2),
% 1.61/0.58    inference(resolution,[],[f195,f45])).
% 1.61/0.58  fof(f195,plain,(
% 1.61/0.58    ( ! [X6,X8,X7,X9] : (~r2_hidden(X8,k2_zfmisc_1(k2_enumset1(X6,X6,X6,X7),X9)) | k1_mcart_1(X8) = X7 | k1_mcart_1(X8) = X6 | X6 = X7) )),
% 1.61/0.58    inference(resolution,[],[f182,f26])).
% 1.61/0.58  fof(f182,plain,(
% 1.61/0.58    ( ! [X4,X2,X3] : (~r2_hidden(X3,k2_enumset1(X2,X2,X2,X4)) | X2 = X4 | X3 = X4 | X2 = X3) )),
% 1.61/0.58    inference(resolution,[],[f104,f54])).
% 1.61/0.58  fof(f54,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 1.61/0.58    inference(definition_unfolding,[],[f40,f44])).
% 1.61/0.58  fof(f40,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f22])).
% 1.61/0.58  fof(f104,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X1,X1,X1,X1))) | X0 = X2 | X0 = X1) )),
% 1.61/0.58    inference(duplicate_literal_removal,[],[f89])).
% 1.61/0.58  fof(f89,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X1,X1,X1,X1))) | X0 = X2 | X0 = X2 | X0 = X2 | X0 = X1) )),
% 1.61/0.58    inference(superposition,[],[f64,f57])).
% 1.61/0.58  fof(f64,plain,(
% 1.61/0.58    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 1.61/0.58    inference(equality_resolution,[],[f53])).
% 1.61/0.58  fof(f53,plain,(
% 1.61/0.58    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.61/0.58    inference(definition_unfolding,[],[f28,f42])).
% 1.61/0.58  fof(f28,plain,(
% 1.61/0.58    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.61/0.58    inference(cnf_transformation,[],[f20])).
% 1.61/0.58  fof(f20,plain,(
% 1.61/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.61/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).
% 1.61/0.58  fof(f19,plain,(
% 1.61/0.58    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.61/0.58    introduced(choice_axiom,[])).
% 1.61/0.58  fof(f18,plain,(
% 1.61/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.61/0.58    inference(rectify,[],[f17])).
% 1.61/0.58  fof(f17,plain,(
% 1.61/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.61/0.58    inference(flattening,[],[f16])).
% 1.61/0.58  fof(f16,plain,(
% 1.61/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.61/0.58    inference(nnf_transformation,[],[f12])).
% 1.61/0.58  fof(f12,plain,(
% 1.61/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.61/0.58    inference(ennf_transformation,[],[f1])).
% 1.61/0.58  fof(f1,axiom,(
% 1.61/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.61/0.58  % SZS output end Proof for theBenchmark
% 1.61/0.58  % (27954)------------------------------
% 1.61/0.58  % (27954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (27954)Termination reason: Refutation
% 1.61/0.58  
% 1.61/0.58  % (27954)Memory used [KB]: 6780
% 1.61/0.58  % (27954)Time elapsed: 0.141 s
% 1.61/0.58  % (27954)------------------------------
% 1.61/0.58  % (27954)------------------------------
% 1.61/0.58  % (27948)Success in time 0.222 s
%------------------------------------------------------------------------------
