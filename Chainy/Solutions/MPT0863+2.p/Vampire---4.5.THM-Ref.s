%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0863+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:54 EST 2020

% Result     : Theorem 1.86s
% Output     : Refutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   35 (  81 expanded)
%              Number of leaves         :    7 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  158 ( 413 expanded)
%              Number of equality atoms :   97 ( 284 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (23626)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_157 on theBenchmark
fof(f1901,plain,(
    $false ),
    inference(global_subsumption,[],[f1612,f1613,f1614,f1615,f1835,f1868])).

fof(f1868,plain,
    ( sQ12_eqProxy(sK2,k1_mcart_1(sK0))
    | sQ12_eqProxy(sK1,k1_mcart_1(sK0)) ),
    inference(resolution,[],[f1800,f1689])).

fof(f1689,plain,(
    ! [X4,X0,X1] :
      ( sQ12_eqProxy(X1,X4)
      | sQ12_eqProxy(X0,X4)
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_proxy_replacement,[],[f1609,f1611,f1611])).

fof(f1611,plain,(
    ! [X1,X0] :
      ( sQ12_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ12_eqProxy])])).

fof(f1609,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f1546])).

fof(f1546,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1427])).

fof(f1427,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK11(X0,X1,X2) != X1
              & sK11(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK11(X0,X1,X2),X2) )
          & ( sK11(X0,X1,X2) = X1
            | sK11(X0,X1,X2) = X0
            | r2_hidden(sK11(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f1425,f1426])).

fof(f1426,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK11(X0,X1,X2) != X1
            & sK11(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK11(X0,X1,X2),X2) )
        & ( sK11(X0,X1,X2) = X1
          | sK11(X0,X1,X2) = X0
          | r2_hidden(sK11(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1425,plain,(
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
    inference(rectify,[],[f1424])).

fof(f1424,plain,(
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
    inference(flattening,[],[f1423])).

fof(f1423,plain,(
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

fof(f1800,plain,(
    r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2)) ),
    inference(resolution,[],[f1428,f1439])).

fof(f1439,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(cnf_transformation,[],[f1319])).

fof(f1319,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f1298])).

fof(f1298,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

fof(f1428,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    inference(cnf_transformation,[],[f1391])).

fof(f1391,plain,
    ( ( ( sK4 != k2_mcart_1(sK0)
        & sK3 != k2_mcart_1(sK0) )
      | ( sK2 != k1_mcart_1(sK0)
        & sK1 != k1_mcart_1(sK0) ) )
    & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f1315,f1390])).

fof(f1390,plain,
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

fof(f1315,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ( ( k2_mcart_1(X0) != X4
          & k2_mcart_1(X0) != X3 )
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) ) ),
    inference(ennf_transformation,[],[f1302])).

fof(f1302,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
       => ( ( k2_mcart_1(X0) = X4
            | k2_mcart_1(X0) = X3 )
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1301])).

fof(f1301,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
     => ( ( k2_mcart_1(X0) = X4
          | k2_mcart_1(X0) = X3 )
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_mcart_1)).

fof(f1835,plain,
    ( sQ12_eqProxy(sK4,k2_mcart_1(sK0))
    | sQ12_eqProxy(sK3,k2_mcart_1(sK0)) ),
    inference(resolution,[],[f1799,f1689])).

fof(f1799,plain,(
    r2_hidden(k2_mcart_1(sK0),k2_tarski(sK3,sK4)) ),
    inference(resolution,[],[f1428,f1438])).

fof(f1438,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k2_mcart_1(X0),X3)
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(cnf_transformation,[],[f1318])).

fof(f1318,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) )
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(ennf_transformation,[],[f1297])).

fof(f1297,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
     => ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

fof(f1615,plain,
    ( ~ sQ12_eqProxy(sK3,k2_mcart_1(sK0))
    | ~ sQ12_eqProxy(sK1,k1_mcart_1(sK0)) ),
    inference(equality_proxy_replacement,[],[f1429,f1611,f1611])).

fof(f1429,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f1391])).

fof(f1614,plain,
    ( ~ sQ12_eqProxy(sK3,k2_mcart_1(sK0))
    | ~ sQ12_eqProxy(sK2,k1_mcart_1(sK0)) ),
    inference(equality_proxy_replacement,[],[f1430,f1611,f1611])).

fof(f1430,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f1391])).

fof(f1613,plain,
    ( ~ sQ12_eqProxy(sK4,k2_mcart_1(sK0))
    | ~ sQ12_eqProxy(sK1,k1_mcart_1(sK0)) ),
    inference(equality_proxy_replacement,[],[f1431,f1611,f1611])).

fof(f1431,plain,
    ( sK4 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f1391])).

fof(f1612,plain,
    ( ~ sQ12_eqProxy(sK4,k2_mcart_1(sK0))
    | ~ sQ12_eqProxy(sK2,k1_mcart_1(sK0)) ),
    inference(equality_proxy_replacement,[],[f1432,f1611,f1611])).

fof(f1432,plain,
    ( sK4 != k2_mcart_1(sK0)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f1391])).
%------------------------------------------------------------------------------
