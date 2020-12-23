%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0859+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:54 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   28 (  49 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :  132 ( 217 expanded)
%              Number of equality atoms :   71 ( 110 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1925,plain,(
    $false ),
    inference(global_subsumption,[],[f1603,f1604,f1705,f1892])).

fof(f1892,plain,
    ( sQ11_eqProxy(sK2,k1_mcart_1(sK0))
    | sQ11_eqProxy(sK1,k1_mcart_1(sK0)) ),
    inference(resolution,[],[f1704,f1676])).

fof(f1676,plain,(
    ! [X4,X0,X1] :
      ( sQ11_eqProxy(X1,X4)
      | sQ11_eqProxy(X0,X4)
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_proxy_replacement,[],[f1600,f1602,f1602])).

fof(f1602,plain,(
    ! [X1,X0] :
      ( sQ11_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ11_eqProxy])])).

fof(f1600,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f1537])).

fof(f1537,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1423])).

fof(f1423,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK10(X0,X1,X2) != X1
              & sK10(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK10(X0,X1,X2),X2) )
          & ( sK10(X0,X1,X2) = X1
            | sK10(X0,X1,X2) = X0
            | r2_hidden(sK10(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f1421,f1422])).

fof(f1422,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK10(X0,X1,X2) != X1
            & sK10(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK10(X0,X1,X2),X2) )
        & ( sK10(X0,X1,X2) = X1
          | sK10(X0,X1,X2) = X0
          | r2_hidden(sK10(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1421,plain,(
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
    inference(rectify,[],[f1420])).

fof(f1420,plain,(
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
    inference(flattening,[],[f1419])).

fof(f1419,plain,(
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

fof(f1704,plain,(
    r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2)) ),
    inference(resolution,[],[f1424,f1434])).

fof(f1434,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f1317])).

fof(f1317,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1292])).

fof(f1292,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f1424,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f1387])).

fof(f1387,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
      | ( sK2 != k1_mcart_1(sK0)
        & sK1 != k1_mcart_1(sK0) ) )
    & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f1311,f1386])).

fof(f1386,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(k2_mcart_1(X0),X3)
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
        | ( sK2 != k1_mcart_1(sK0)
          & sK1 != k1_mcart_1(sK0) ) )
      & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f1311,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X3)
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(ennf_transformation,[],[f1298])).

fof(f1298,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
       => ( r2_hidden(k2_mcart_1(X0),X3)
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1297])).

fof(f1297,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
     => ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

fof(f1705,plain,(
    r2_hidden(k2_mcart_1(sK0),sK3) ),
    inference(resolution,[],[f1424,f1435])).

fof(f1435,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f1317])).

fof(f1604,plain,
    ( ~ sQ11_eqProxy(sK1,k1_mcart_1(sK0))
    | ~ r2_hidden(k2_mcart_1(sK0),sK3) ),
    inference(equality_proxy_replacement,[],[f1425,f1602])).

fof(f1425,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f1387])).

fof(f1603,plain,
    ( ~ sQ11_eqProxy(sK2,k1_mcart_1(sK0))
    | ~ r2_hidden(k2_mcart_1(sK0),sK3) ),
    inference(equality_proxy_replacement,[],[f1426,f1602])).

fof(f1426,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f1387])).
%------------------------------------------------------------------------------
