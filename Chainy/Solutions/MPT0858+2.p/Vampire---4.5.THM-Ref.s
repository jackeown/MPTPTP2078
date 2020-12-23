%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0858+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  51 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 186 expanded)
%              Number of equality atoms :   46 ( 100 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1674,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1670,f1591])).

fof(f1591,plain,(
    r2_hidden(k1_mcart_1(sK0),k1_tarski(sK1)) ),
    inference(resolution,[],[f1399,f1404])).

fof(f1404,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f1316])).

fof(f1316,plain,(
    ! [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f1295])).

fof(f1295,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

fof(f1399,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f1369])).

fof(f1369,plain,
    ( ( sK2 != k2_mcart_1(sK0)
      | sK1 != k1_mcart_1(sK0) )
    & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1312,f1368])).

fof(f1368,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_mcart_1(X0) != X2
          | k1_mcart_1(X0) != X1 )
        & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))) )
   => ( ( sK2 != k2_mcart_1(sK0)
        | sK1 != k1_mcart_1(sK0) )
      & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f1312,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) != X2
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f1297])).

fof(f1297,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)))
       => ( k2_mcart_1(X0) = X2
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f1296])).

fof(f1296,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_mcart_1)).

fof(f1670,plain,(
    ~ r2_hidden(k1_mcart_1(sK0),k1_tarski(sK1)) ),
    inference(resolution,[],[f1662,f1575])).

fof(f1575,plain,(
    ! [X0,X3] :
      ( sQ12_eqProxy(X0,X3)
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_proxy_replacement,[],[f1519,f1520])).

fof(f1520,plain,(
    ! [X1,X0] :
      ( sQ12_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ12_eqProxy])])).

fof(f1519,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f1484])).

fof(f1484,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1398])).

fof(f1398,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK11(X0,X1) != X0
            | ~ r2_hidden(sK11(X0,X1),X1) )
          & ( sK11(X0,X1) = X0
            | r2_hidden(sK11(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f1396,f1397])).

fof(f1397,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK11(X0,X1) != X0
          | ~ r2_hidden(sK11(X0,X1),X1) )
        & ( sK11(X0,X1) = X0
          | r2_hidden(sK11(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1396,plain,(
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
    inference(rectify,[],[f1395])).

fof(f1395,plain,(
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

fof(f1662,plain,(
    ~ sQ12_eqProxy(sK1,k1_mcart_1(sK0)) ),
    inference(global_subsumption,[],[f1521,f1623])).

fof(f1623,plain,(
    sQ12_eqProxy(sK2,k2_mcart_1(sK0)) ),
    inference(resolution,[],[f1590,f1575])).

fof(f1590,plain,(
    r2_hidden(k2_mcart_1(sK0),k1_tarski(sK2)) ),
    inference(resolution,[],[f1399,f1403])).

fof(f1403,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f1315])).

fof(f1315,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f1294])).

fof(f1294,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f1521,plain,
    ( ~ sQ12_eqProxy(sK2,k2_mcart_1(sK0))
    | ~ sQ12_eqProxy(sK1,k1_mcart_1(sK0)) ),
    inference(equality_proxy_replacement,[],[f1400,f1520,f1520])).

fof(f1400,plain,
    ( sK2 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f1369])).
%------------------------------------------------------------------------------
