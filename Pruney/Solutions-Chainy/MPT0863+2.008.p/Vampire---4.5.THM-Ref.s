%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:30 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 153 expanded)
%              Number of leaves         :   11 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  196 ( 498 expanded)
%              Number of equality atoms :   98 ( 334 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f161,plain,(
    $false ),
    inference(subsumption_resolution,[],[f160,f115])).

fof(f115,plain,(
    sK1 != k1_mcart_1(sK0) ),
    inference(subsumption_resolution,[],[f112,f21])).

fof(f21,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( ( sK4 != k2_mcart_1(sK0)
        & sK3 != k2_mcart_1(sK0) )
      | ( sK2 != k1_mcart_1(sK0)
        & sK1 != k1_mcart_1(sK0) ) )
    & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ( ( k2_mcart_1(X0) != X4
            & k2_mcart_1(X0) != X3 )
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) )
   => ( ( ( sK4 != k2_mcart_1(sK0)
          & sK3 != k2_mcart_1(sK0) )
        | ( sK2 != k1_mcart_1(sK0)
          & sK1 != k1_mcart_1(sK0) ) )
      & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ( ( k2_mcart_1(X0) != X4
          & k2_mcart_1(X0) != X3 )
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
       => ( ( k2_mcart_1(X0) = X4
            | k2_mcart_1(X0) = X3 )
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
     => ( ( k2_mcart_1(X0) = X4
          | k2_mcart_1(X0) = X3 )
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_mcart_1)).

fof(f112,plain,
    ( sK1 != k1_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(trivial_inequality_removal,[],[f108])).

fof(f108,plain,
    ( sK4 != sK4
    | sK1 != k1_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(superposition,[],[f23,f101])).

fof(f101,plain,
    ( sK4 = k2_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(resolution,[],[f43,f42])).

fof(f42,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK3,sK3,sK3,sK4))) ),
    inference(definition_unfolding,[],[f20,f41,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X3)))
      | k2_mcart_1(X0) = X2
      | k2_mcart_1(X0) = X3 ) ),
    inference(definition_unfolding,[],[f26,f41])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X0) = X3
      | k2_mcart_1(X0) = X2
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_mcart_1)).

fof(f23,plain,
    ( sK4 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f160,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(subsumption_resolution,[],[f157,f114])).

fof(f114,plain,(
    sK2 != k1_mcart_1(sK0) ),
    inference(subsumption_resolution,[],[f113,f22])).

fof(f22,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f113,plain,
    ( sK2 != k1_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(trivial_inequality_removal,[],[f107])).

fof(f107,plain,
    ( sK4 != sK4
    | sK2 != k1_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(superposition,[],[f24,f101])).

fof(f24,plain,
    ( sK4 != k2_mcart_1(sK0)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f157,plain,
    ( sK2 = k1_mcart_1(sK0)
    | sK1 = k1_mcart_1(sK0) ),
    inference(superposition,[],[f142,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f142,plain,
    ( sK2 = k2_mcart_1(k4_tarski(k2_mcart_1(sK0),k1_mcart_1(sK0)))
    | sK1 = k2_mcart_1(k4_tarski(k2_mcart_1(sK0),k1_mcart_1(sK0))) ),
    inference(resolution,[],[f60,f43])).

fof(f60,plain,(
    r2_hidden(k4_tarski(k2_mcart_1(sK0),k1_mcart_1(sK0)),k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK1,sK1,sK1,sK2))) ),
    inference(resolution,[],[f56,f53])).

fof(f53,plain,(
    r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(resolution,[],[f42,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f56,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | r2_hidden(k4_tarski(k2_mcart_1(sK0),X2),k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK4),X3)) ) ),
    inference(resolution,[],[f46,f52])).

fof(f52,plain,(
    r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(resolution,[],[f42,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X0,X10,X1,X9] :
      ( ~ r2_hidden(X9,X0)
      | ~ r2_hidden(X10,X1)
      | r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK5(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2))
              & r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8
                & r2_hidden(sK9(X0,X1,X8),X1)
                & r2_hidden(sK8(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f15,f18,f17,f16])).

fof(f16,plain,(
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
              ( k4_tarski(X4,X5) != sK5(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK5(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK5(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2))
        & r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(sK6(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8
        & r2_hidden(sK9(X0,X1,X8),X1)
        & r2_hidden(sK8(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:05:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.20/0.52  % (31433)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.20/0.52  % (31431)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.20/0.52  % (31426)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.20/0.53  % (31433)Refutation not found, incomplete strategy% (31433)------------------------------
% 1.20/0.53  % (31433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (31427)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.53  % (31425)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.28/0.53  % (31447)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.28/0.53  % (31425)Refutation not found, incomplete strategy% (31425)------------------------------
% 1.28/0.53  % (31425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (31441)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.28/0.53  % (31425)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (31425)Memory used [KB]: 1663
% 1.28/0.53  % (31425)Time elapsed: 0.108 s
% 1.28/0.53  % (31425)------------------------------
% 1.28/0.53  % (31425)------------------------------
% 1.28/0.54  % (31445)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.28/0.54  % (31430)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.28/0.54  % (31433)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (31433)Memory used [KB]: 10746
% 1.28/0.54  % (31433)Time elapsed: 0.104 s
% 1.28/0.54  % (31433)------------------------------
% 1.28/0.54  % (31433)------------------------------
% 1.28/0.54  % (31429)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.28/0.54  % (31450)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.28/0.54  % (31442)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.28/0.54  % (31444)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.28/0.54  % (31430)Refutation found. Thanks to Tanya!
% 1.28/0.54  % SZS status Theorem for theBenchmark
% 1.28/0.54  % SZS output start Proof for theBenchmark
% 1.28/0.54  fof(f161,plain,(
% 1.28/0.54    $false),
% 1.28/0.54    inference(subsumption_resolution,[],[f160,f115])).
% 1.28/0.54  fof(f115,plain,(
% 1.28/0.54    sK1 != k1_mcart_1(sK0)),
% 1.28/0.54    inference(subsumption_resolution,[],[f112,f21])).
% 1.28/0.54  fof(f21,plain,(
% 1.28/0.54    sK3 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 1.28/0.54    inference(cnf_transformation,[],[f13])).
% 1.28/0.54  fof(f13,plain,(
% 1.28/0.54    ((sK4 != k2_mcart_1(sK0) & sK3 != k2_mcart_1(sK0)) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 1.28/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f12])).
% 1.28/0.54  fof(f12,plain,(
% 1.28/0.54    ? [X0,X1,X2,X3,X4] : (((k2_mcart_1(X0) != X4 & k2_mcart_1(X0) != X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))) => (((sK4 != k2_mcart_1(sK0) & sK3 != k2_mcart_1(sK0)) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))))),
% 1.28/0.54    introduced(choice_axiom,[])).
% 1.28/0.54  fof(f9,plain,(
% 1.28/0.54    ? [X0,X1,X2,X3,X4] : (((k2_mcart_1(X0) != X4 & k2_mcart_1(X0) != X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))))),
% 1.28/0.54    inference(ennf_transformation,[],[f8])).
% 1.28/0.54  fof(f8,negated_conjecture,(
% 1.28/0.54    ~! [X0,X1,X2,X3,X4] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) => ((k2_mcart_1(X0) = X4 | k2_mcart_1(X0) = X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 1.28/0.54    inference(negated_conjecture,[],[f7])).
% 1.28/0.54  fof(f7,conjecture,(
% 1.28/0.54    ! [X0,X1,X2,X3,X4] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) => ((k2_mcart_1(X0) = X4 | k2_mcart_1(X0) = X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 1.28/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_mcart_1)).
% 1.28/0.54  fof(f112,plain,(
% 1.28/0.54    sK1 != k1_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 1.28/0.54    inference(trivial_inequality_removal,[],[f108])).
% 1.28/0.54  fof(f108,plain,(
% 1.28/0.54    sK4 != sK4 | sK1 != k1_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 1.28/0.54    inference(superposition,[],[f23,f101])).
% 1.28/0.54  fof(f101,plain,(
% 1.28/0.54    sK4 = k2_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 1.28/0.54    inference(resolution,[],[f43,f42])).
% 1.28/0.54  fof(f42,plain,(
% 1.28/0.54    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK3,sK3,sK3,sK4)))),
% 1.28/0.54    inference(definition_unfolding,[],[f20,f41,f41])).
% 1.28/0.54  fof(f41,plain,(
% 1.28/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.28/0.54    inference(definition_unfolding,[],[f39,f40])).
% 1.28/0.54  fof(f40,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f2])).
% 1.28/0.54  fof(f2,axiom,(
% 1.28/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.28/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.28/0.54  fof(f39,plain,(
% 1.28/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f1])).
% 1.28/0.54  fof(f1,axiom,(
% 1.28/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.28/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.28/0.54  fof(f20,plain,(
% 1.28/0.54    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 1.28/0.54    inference(cnf_transformation,[],[f13])).
% 1.28/0.54  fof(f43,plain,(
% 1.28/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X3))) | k2_mcart_1(X0) = X2 | k2_mcart_1(X0) = X3) )),
% 1.28/0.54    inference(definition_unfolding,[],[f26,f41])).
% 1.28/0.54  fof(f26,plain,(
% 1.28/0.54    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2 | ~r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))) )),
% 1.28/0.54    inference(cnf_transformation,[],[f10])).
% 1.28/0.54  fof(f10,plain,(
% 1.28/0.54    ! [X0,X1,X2,X3] : (((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))))),
% 1.28/0.54    inference(ennf_transformation,[],[f5])).
% 1.28/0.54  fof(f5,axiom,(
% 1.28/0.54    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.28/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_mcart_1)).
% 1.28/0.54  fof(f23,plain,(
% 1.28/0.54    sK4 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 1.28/0.54    inference(cnf_transformation,[],[f13])).
% 1.28/0.54  fof(f160,plain,(
% 1.28/0.54    sK1 = k1_mcart_1(sK0)),
% 1.28/0.54    inference(subsumption_resolution,[],[f157,f114])).
% 1.28/0.54  fof(f114,plain,(
% 1.28/0.54    sK2 != k1_mcart_1(sK0)),
% 1.28/0.54    inference(subsumption_resolution,[],[f113,f22])).
% 1.28/0.54  fof(f22,plain,(
% 1.28/0.54    sK3 != k2_mcart_1(sK0) | sK2 != k1_mcart_1(sK0)),
% 1.28/0.54    inference(cnf_transformation,[],[f13])).
% 1.28/0.54  fof(f113,plain,(
% 1.28/0.54    sK2 != k1_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 1.28/0.54    inference(trivial_inequality_removal,[],[f107])).
% 1.28/0.54  fof(f107,plain,(
% 1.28/0.54    sK4 != sK4 | sK2 != k1_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 1.28/0.54    inference(superposition,[],[f24,f101])).
% 1.28/0.54  fof(f24,plain,(
% 1.28/0.54    sK4 != k2_mcart_1(sK0) | sK2 != k1_mcart_1(sK0)),
% 1.28/0.54    inference(cnf_transformation,[],[f13])).
% 1.28/0.54  fof(f157,plain,(
% 1.28/0.54    sK2 = k1_mcart_1(sK0) | sK1 = k1_mcart_1(sK0)),
% 1.28/0.54    inference(superposition,[],[f142,f30])).
% 1.28/0.54  fof(f30,plain,(
% 1.28/0.54    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.28/0.54    inference(cnf_transformation,[],[f6])).
% 1.28/0.54  fof(f6,axiom,(
% 1.28/0.54    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.28/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.28/0.54  fof(f142,plain,(
% 1.28/0.54    sK2 = k2_mcart_1(k4_tarski(k2_mcart_1(sK0),k1_mcart_1(sK0))) | sK1 = k2_mcart_1(k4_tarski(k2_mcart_1(sK0),k1_mcart_1(sK0)))),
% 1.28/0.54    inference(resolution,[],[f60,f43])).
% 1.28/0.54  fof(f60,plain,(
% 1.28/0.54    r2_hidden(k4_tarski(k2_mcart_1(sK0),k1_mcart_1(sK0)),k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK1,sK1,sK1,sK2)))),
% 1.28/0.54    inference(resolution,[],[f56,f53])).
% 1.28/0.54  fof(f53,plain,(
% 1.28/0.54    r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.28/0.54    inference(resolution,[],[f42,f27])).
% 1.28/0.54  fof(f27,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f11])).
% 1.28/0.54  fof(f11,plain,(
% 1.28/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.28/0.54    inference(ennf_transformation,[],[f4])).
% 1.28/0.54  fof(f4,axiom,(
% 1.28/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.28/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.28/0.54  fof(f56,plain,(
% 1.28/0.54    ( ! [X2,X3] : (~r2_hidden(X2,X3) | r2_hidden(k4_tarski(k2_mcart_1(sK0),X2),k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK4),X3))) )),
% 1.28/0.54    inference(resolution,[],[f46,f52])).
% 1.28/0.54  fof(f52,plain,(
% 1.28/0.54    r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK3,sK3,sK3,sK4))),
% 1.28/0.54    inference(resolution,[],[f42,f28])).
% 1.28/0.54  fof(f28,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f11])).
% 1.28/0.54  fof(f46,plain,(
% 1.28/0.54    ( ! [X0,X10,X1,X9] : (~r2_hidden(X9,X0) | ~r2_hidden(X10,X1) | r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))) )),
% 1.28/0.54    inference(equality_resolution,[],[f45])).
% 1.28/0.54  fof(f45,plain,(
% 1.28/0.54    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.28/0.54    inference(equality_resolution,[],[f34])).
% 1.28/0.54  fof(f34,plain,(
% 1.28/0.54    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.28/0.54    inference(cnf_transformation,[],[f19])).
% 1.28/0.54  fof(f19,plain,(
% 1.28/0.54    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK5(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8 & r2_hidden(sK9(X0,X1,X8),X1) & r2_hidden(sK8(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.28/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f15,f18,f17,f16])).
% 1.28/0.54  fof(f16,plain,(
% 1.28/0.54    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK5(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK5(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.28/0.54    introduced(choice_axiom,[])).
% 1.28/0.54  fof(f17,plain,(
% 1.28/0.54    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK5(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)))),
% 1.28/0.54    introduced(choice_axiom,[])).
% 1.28/0.54  fof(f18,plain,(
% 1.28/0.54    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8 & r2_hidden(sK9(X0,X1,X8),X1) & r2_hidden(sK8(X0,X1,X8),X0)))),
% 1.28/0.54    introduced(choice_axiom,[])).
% 1.28/0.54  fof(f15,plain,(
% 1.28/0.54    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.28/0.54    inference(rectify,[],[f14])).
% 1.28/0.54  fof(f14,plain,(
% 1.28/0.54    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.28/0.54    inference(nnf_transformation,[],[f3])).
% 1.28/0.54  fof(f3,axiom,(
% 1.28/0.54    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.28/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.28/0.54  % SZS output end Proof for theBenchmark
% 1.28/0.54  % (31430)------------------------------
% 1.28/0.54  % (31430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (31430)Termination reason: Refutation
% 1.28/0.54  
% 1.28/0.54  % (31430)Memory used [KB]: 6396
% 1.28/0.54  % (31430)Time elapsed: 0.121 s
% 1.28/0.54  % (31430)------------------------------
% 1.28/0.54  % (31430)------------------------------
% 1.28/0.54  % (31442)Refutation not found, incomplete strategy% (31442)------------------------------
% 1.28/0.54  % (31442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (31442)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (31442)Memory used [KB]: 10618
% 1.28/0.54  % (31442)Time elapsed: 0.097 s
% 1.28/0.54  % (31442)------------------------------
% 1.28/0.54  % (31442)------------------------------
% 1.28/0.54  % (31428)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.28/0.54  % (31424)Success in time 0.177 s
%------------------------------------------------------------------------------
