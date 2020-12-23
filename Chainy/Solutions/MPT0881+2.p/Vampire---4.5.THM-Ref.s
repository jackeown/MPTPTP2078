%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0881+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:55 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   43 (  80 expanded)
%              Number of leaves         :   11 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  157 ( 195 expanded)
%              Number of equality atoms :  108 ( 146 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4150,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4149,f3818])).

fof(f3818,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f3817])).

fof(f3817,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f3489])).

fof(f3489,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f2453,f2477])).

fof(f2477,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f262])).

fof(f262,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f2453,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1930])).

fof(f1930,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK8(X0,X1,X2) != X1
              & sK8(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( sK8(X0,X1,X2) = X1
            | sK8(X0,X1,X2) = X0
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f1928,f1929])).

fof(f1929,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK8(X0,X1,X2) != X1
            & sK8(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( sK8(X0,X1,X2) = X1
          | sK8(X0,X1,X2) = X0
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1928,plain,(
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
    inference(rectify,[],[f1927])).

fof(f1927,plain,(
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
    inference(flattening,[],[f1926])).

fof(f1926,plain,(
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
    inference(nnf_transformation,[],[f176])).

fof(f176,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f4149,plain,(
    ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK5)),k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK5)),k2_enumset1(sK6,sK6,sK6,sK6)),k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK5)),k2_enumset1(sK6,sK6,sK6,sK6)),k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK5)),k2_enumset1(sK6,sK6,sK6,sK6)),k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK5)),k2_enumset1(sK6,sK6,sK6,sK6)))) ),
    inference(forward_demodulation,[],[f4148,f3506])).

fof(f3506,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(definition_unfolding,[],[f2470,f3414,f2477,f2477])).

fof(f3414,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f2488,f2477])).

fof(f2488,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

% (12897)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f2470,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f394])).

fof(f394,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f4148,plain,(
    ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK5)),k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(k2_zfmisc_1(k2_enumset1(k4_tarski(sK3,sK4),k4_tarski(sK3,sK4),k4_tarski(sK3,sK4),k4_tarski(sK3,sK5)),k2_enumset1(sK6,sK6,sK6,sK6)),k2_zfmisc_1(k2_enumset1(k4_tarski(sK3,sK4),k4_tarski(sK3,sK4),k4_tarski(sK3,sK4),k4_tarski(sK3,sK5)),k2_enumset1(sK6,sK6,sK6,sK6)),k2_zfmisc_1(k2_enumset1(k4_tarski(sK3,sK4),k4_tarski(sK3,sK4),k4_tarski(sK3,sK4),k4_tarski(sK3,sK5)),k2_enumset1(sK6,sK6,sK6,sK6)),k2_zfmisc_1(k2_enumset1(k4_tarski(sK3,sK4),k4_tarski(sK3,sK4),k4_tarski(sK3,sK4),k4_tarski(sK3,sK5)),k2_enumset1(sK6,sK6,sK6,sK6)))) ),
    inference(forward_demodulation,[],[f4138,f3505])).

fof(f3505,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f2471,f2477,f3414,f2477])).

fof(f2471,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f394])).

fof(f4138,plain,(
    ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK5)),k2_enumset1(sK6,sK6,sK6,sK6)),k2_enumset1(k2_enumset1(k4_tarski(k4_tarski(sK3,sK4),sK6),k4_tarski(k4_tarski(sK3,sK4),sK6),k4_tarski(k4_tarski(sK3,sK4),sK6),k4_tarski(k4_tarski(sK3,sK5),sK6)),k2_enumset1(k4_tarski(k4_tarski(sK3,sK4),sK6),k4_tarski(k4_tarski(sK3,sK4),sK6),k4_tarski(k4_tarski(sK3,sK4),sK6),k4_tarski(k4_tarski(sK3,sK5),sK6)),k2_enumset1(k4_tarski(k4_tarski(sK3,sK4),sK6),k4_tarski(k4_tarski(sK3,sK4),sK6),k4_tarski(k4_tarski(sK3,sK4),sK6),k4_tarski(k4_tarski(sK3,sK5),sK6)),k2_enumset1(k4_tarski(k4_tarski(sK3,sK4),sK6),k4_tarski(k4_tarski(sK3,sK4),sK6),k4_tarski(k4_tarski(sK3,sK4),sK6),k4_tarski(k4_tarski(sK3,sK5),sK6)))) ),
    inference(unit_resulting_resolution,[],[f3418,f3838])).

fof(f3838,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f3586])).

fof(f3586,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f2552,f3414])).

fof(f2552,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1960])).

fof(f1960,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK12(X0,X1) != X0
            | ~ r2_hidden(sK12(X0,X1),X1) )
          & ( sK12(X0,X1) = X0
            | r2_hidden(sK12(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f1958,f1959])).

% (12887)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
fof(f1959,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK12(X0,X1) != X0
          | ~ r2_hidden(sK12(X0,X1),X1) )
        & ( sK12(X0,X1) = X0
          | r2_hidden(sK12(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1958,plain,(
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
    inference(rectify,[],[f1957])).

fof(f1957,plain,(
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
    inference(nnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f3418,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK5)),k2_enumset1(sK6,sK6,sK6,sK6)) != k2_enumset1(k4_tarski(k4_tarski(sK3,sK4),sK6),k4_tarski(k4_tarski(sK3,sK4),sK6),k4_tarski(k4_tarski(sK3,sK4),sK6),k4_tarski(k4_tarski(sK3,sK5),sK6)) ),
    inference(definition_unfolding,[],[f2378,f2400,f3414,f2477,f3414,f2477,f2386,f2386])).

fof(f2386,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1274])).

fof(f1274,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

% (12885)dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34 on theBenchmark
fof(f2400,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1275])).

fof(f1275,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f2378,plain,(
    k3_zfmisc_1(k1_tarski(sK3),k2_tarski(sK4,sK5),k1_tarski(sK6)) != k2_tarski(k3_mcart_1(sK3,sK4,sK6),k3_mcart_1(sK3,sK5,sK6)) ),
    inference(cnf_transformation,[],[f1905])).

fof(f1905,plain,(
    k3_zfmisc_1(k1_tarski(sK3),k2_tarski(sK4,sK5),k1_tarski(sK6)) != k2_tarski(k3_mcart_1(sK3,sK4,sK6),k3_mcart_1(sK3,sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f1345,f1904])).

fof(f1904,plain,
    ( ? [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k1_tarski(X3)) != k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3))
   => k3_zfmisc_1(k1_tarski(sK3),k2_tarski(sK4,sK5),k1_tarski(sK6)) != k2_tarski(k3_mcart_1(sK3,sK4,sK6),k3_mcart_1(sK3,sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f1345,plain,(
    ? [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k1_tarski(X3)) != k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3)) ),
    inference(ennf_transformation,[],[f1329])).

fof(f1329,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3)) ),
    inference(negated_conjecture,[],[f1328])).

fof(f1328,conjecture,(
    ! [X0,X1,X2,X3] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_mcart_1)).
%------------------------------------------------------------------------------
