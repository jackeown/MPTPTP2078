%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0565+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:37 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 146 expanded)
%              Number of leaves         :   13 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  197 ( 625 expanded)
%              Number of equality atoms :   25 ( 101 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1200,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1199,f1170])).

fof(f1170,plain,(
    ! [X2] : ~ r2_hidden(k4_tarski(sK10(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X2),sK0) ),
    inference(subsumption_resolution,[],[f1168,f937])).

fof(f937,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f903])).

fof(f903,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f870])).

fof(f870,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f866,f869,f868,f867])).

fof(f867,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f868,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f869,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f866,plain,(
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
    inference(rectify,[],[f865])).

fof(f865,plain,(
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
    inference(nnf_transformation,[],[f649])).

fof(f649,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f1168,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_relat_1(sK0))
      | ~ r2_hidden(k4_tarski(sK10(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X2),sK0) ) ),
    inference(condensation,[],[f1162])).

fof(f1162,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(sK10(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X1),sK0)
      | ~ r2_hidden(X2,k2_relat_1(sK0))
      | ~ r2_hidden(k4_tarski(sK10(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X2),sK0) ) ),
    inference(resolution,[],[f997,f992])).

fof(f992,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(X6,k10_relat_1(sK0,X7))
      | ~ r2_hidden(X8,X7)
      | ~ r2_hidden(k4_tarski(X6,X8),sK0) ) ),
    inference(subsumption_resolution,[],[f968,f937])).

fof(f968,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(X6,k10_relat_1(sK0,X7))
      | ~ r2_hidden(X8,X7)
      | ~ r2_hidden(k4_tarski(X6,X8),sK0)
      | ~ r2_hidden(X8,k2_relat_1(sK0)) ) ),
    inference(resolution,[],[f882,f887])).

fof(f887,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f858])).

fof(f858,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2)
            & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f856,f857])).

fof(f857,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2)
        & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f856,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f855])).

fof(f855,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f822])).

fof(f822,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f749])).

fof(f749,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f882,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f854])).

fof(f854,plain,
    ( k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f821,f853])).

fof(f853,plain,
    ( ? [X0] :
        ( k1_relat_1(X0) != k10_relat_1(X0,k2_relat_1(X0))
        & v1_relat_1(X0) )
   => ( k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f821,plain,(
    ? [X0] :
      ( k1_relat_1(X0) != k10_relat_1(X0,k2_relat_1(X0))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f753])).

fof(f753,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(negated_conjecture,[],[f752])).

fof(f752,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f997,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK10(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k10_relat_1(sK0,k2_relat_1(sK0)))
      | ~ r2_hidden(k4_tarski(sK10(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),X0),sK0) ) ),
    inference(resolution,[],[f942,f961])).

fof(f961,plain,(
    ! [X0,X3,X1] :
      ( sQ13_eqProxy(k1_relat_1(X0),X1)
      | ~ r2_hidden(k4_tarski(sK10(X0,X1),X3),X0)
      | ~ r2_hidden(sK10(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f925,f941])).

fof(f941,plain,(
    ! [X1,X0] :
      ( sQ13_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ13_eqProxy])])).

fof(f925,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK10(X0,X1),X3),X0)
      | ~ r2_hidden(sK10(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f881])).

fof(f881,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK10(X0,X1),X3),X0)
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0)
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f877,f880,f879,f878])).

fof(f878,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK10(X0,X1),X3),X0)
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0)
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f879,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f880,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f877,plain,(
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
    inference(rectify,[],[f876])).

fof(f876,plain,(
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
    inference(nnf_transformation,[],[f648])).

fof(f648,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f942,plain,(
    ~ sQ13_eqProxy(k1_relat_1(sK0),k10_relat_1(sK0,k2_relat_1(sK0))) ),
    inference(equality_proxy_replacement,[],[f883,f941])).

fof(f883,plain,(
    k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f854])).

fof(f1199,plain,(
    r2_hidden(k4_tarski(sK10(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),sK11(sK0,k10_relat_1(sK0,k2_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f1194,f942])).

fof(f1194,plain,
    ( sQ13_eqProxy(k1_relat_1(sK0),k10_relat_1(sK0,k2_relat_1(sK0)))
    | r2_hidden(k4_tarski(sK10(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),sK11(sK0,k10_relat_1(sK0,k2_relat_1(sK0)))),sK0) ),
    inference(resolution,[],[f1172,f962])).

fof(f962,plain,(
    ! [X0,X1] :
      ( sQ13_eqProxy(k1_relat_1(X0),X1)
      | r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0)
      | r2_hidden(sK10(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f924,f941])).

fof(f924,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0)
      | r2_hidden(sK10(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f881])).

fof(f1172,plain,(
    ! [X0] : ~ r2_hidden(sK10(sK0,k10_relat_1(sK0,k2_relat_1(sK0))),k10_relat_1(sK0,X0)) ),
    inference(resolution,[],[f1170,f966])).

fof(f966,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(X2,sK1(X2,X3,sK0)),sK0)
      | ~ r2_hidden(X2,k10_relat_1(sK0,X3)) ) ),
    inference(resolution,[],[f882,f885])).

fof(f885,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f858])).
%------------------------------------------------------------------------------
