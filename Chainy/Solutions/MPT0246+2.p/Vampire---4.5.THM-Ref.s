%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0246+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:19 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   29 (  61 expanded)
%              Number of leaves         :    5 (  23 expanded)
%              Depth                    :   13
%              Number of atoms          :   79 ( 191 expanded)
%              Number of equality atoms :   38 ( 114 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1513,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1512,f1189])).

fof(f1189,plain,(
    ~ sQ36_eqProxy(sK4,k1_tarski(sK5)) ),
    inference(equality_proxy_replacement,[],[f629,f1171])).

fof(f1171,plain,(
    ! [X1,X0] :
      ( sQ36_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ36_eqProxy])])).

fof(f629,plain,(
    sK4 != k1_tarski(sK5) ),
    inference(cnf_transformation,[],[f501])).

fof(f501,plain,
    ( ! [X2] :
        ( sK5 = X2
        | ~ r2_hidden(X2,sK4) )
    & k1_xboole_0 != sK4
    & sK4 != k1_tarski(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f353,f500])).

fof(f500,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( X1 = X2
            | ~ r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 )
   => ( ! [X2] :
          ( sK5 = X2
          | ~ r2_hidden(X2,sK4) )
      & k1_xboole_0 != sK4
      & sK4 != k1_tarski(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f353,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f343])).

fof(f343,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f342])).

fof(f342,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f1512,plain,(
    sQ36_eqProxy(sK4,k1_tarski(sK5)) ),
    inference(resolution,[],[f1511,f1452])).

fof(f1452,plain,(
    ! [X0,X1] :
      ( ~ sQ36_eqProxy(X0,X1)
      | sQ36_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f1171])).

fof(f1511,plain,(
    sQ36_eqProxy(k1_tarski(sK5),sK4) ),
    inference(subsumption_resolution,[],[f1510,f1188])).

fof(f1188,plain,(
    ~ sQ36_eqProxy(k1_xboole_0,sK4) ),
    inference(equality_proxy_replacement,[],[f630,f1171])).

fof(f630,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f501])).

fof(f1510,plain,
    ( sQ36_eqProxy(k1_tarski(sK5),sK4)
    | sQ36_eqProxy(k1_xboole_0,sK4) ),
    inference(duplicate_literal_removal,[],[f1508])).

fof(f1508,plain,
    ( sQ36_eqProxy(k1_tarski(sK5),sK4)
    | sQ36_eqProxy(k1_xboole_0,sK4)
    | sQ36_eqProxy(k1_tarski(sK5),sK4) ),
    inference(resolution,[],[f1506,f1293])).

fof(f1293,plain,(
    ! [X0,X1] :
      ( ~ sQ36_eqProxy(sK18(X0,X1),X1)
      | sQ36_eqProxy(k1_xboole_0,X0)
      | sQ36_eqProxy(k1_tarski(X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f816,f1171,f1171,f1171])).

fof(f816,plain,(
    ! [X0,X1] :
      ( sK18(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f557])).

fof(f557,plain,(
    ! [X0,X1] :
      ( ( sK18(X0,X1) != X1
        & r2_hidden(sK18(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f401,f556])).

fof(f556,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK18(X0,X1) != X1
        & r2_hidden(sK18(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f401,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f306])).

fof(f306,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f1506,plain,(
    ! [X0] :
      ( sQ36_eqProxy(sK18(sK4,X0),sK5)
      | sQ36_eqProxy(k1_tarski(X0),sK4) ) ),
    inference(resolution,[],[f1492,f1452])).

fof(f1492,plain,(
    ! [X4] :
      ( sQ36_eqProxy(sK5,sK18(sK4,X4))
      | sQ36_eqProxy(k1_tarski(X4),sK4) ) ),
    inference(subsumption_resolution,[],[f1477,f1188])).

fof(f1477,plain,(
    ! [X4] :
      ( sQ36_eqProxy(sK5,sK18(sK4,X4))
      | sQ36_eqProxy(k1_xboole_0,sK4)
      | sQ36_eqProxy(k1_tarski(X4),sK4) ) ),
    inference(resolution,[],[f1187,f1294])).

fof(f1294,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK18(X0,X1),X0)
      | sQ36_eqProxy(k1_xboole_0,X0)
      | sQ36_eqProxy(k1_tarski(X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f815,f1171,f1171])).

fof(f815,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK18(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f557])).

fof(f1187,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK4)
      | sQ36_eqProxy(sK5,X2) ) ),
    inference(equality_proxy_replacement,[],[f631,f1171])).

fof(f631,plain,(
    ! [X2] :
      ( sK5 = X2
      | ~ r2_hidden(X2,sK4) ) ),
    inference(cnf_transformation,[],[f501])).
%------------------------------------------------------------------------------
