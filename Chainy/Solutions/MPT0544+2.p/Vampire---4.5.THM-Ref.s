%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0544+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:36 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 120 expanded)
%              Number of leaves         :   13 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  211 ( 534 expanded)
%              Number of equality atoms :   27 (  86 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1364,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1360,f1344])).

fof(f1344,plain,(
    ! [X2] : ~ r2_hidden(k4_tarski(X2,sK8(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f1342,f909])).

fof(f909,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f872])).

fof(f872,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f845])).

fof(f845,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f841,f844,f843,f842])).

fof(f842,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f843,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f844,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f841,plain,(
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
    inference(rectify,[],[f840])).

fof(f840,plain,(
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
    inference(nnf_transformation,[],[f647])).

fof(f647,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f1342,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK0))
      | ~ r2_hidden(k4_tarski(X2,sK8(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0) ) ),
    inference(condensation,[],[f1336])).

fof(f1336,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(X1,sK8(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)
      | ~ r2_hidden(X2,k1_relat_1(sK0))
      | ~ r2_hidden(k4_tarski(X2,sK8(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0) ) ),
    inference(resolution,[],[f975,f970])).

fof(f970,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(X6,k9_relat_1(sK0,X7))
      | ~ r2_hidden(X8,X7)
      | ~ r2_hidden(k4_tarski(X8,X6),sK0) ) ),
    inference(subsumption_resolution,[],[f944,f909])).

fof(f944,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(X6,k9_relat_1(sK0,X7))
      | ~ r2_hidden(X8,X7)
      | ~ r2_hidden(k4_tarski(X8,X6),sK0)
      | ~ r2_hidden(X8,k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f857,f862])).

fof(f862,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f833])).

fof(f833,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
            & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f831,f832])).

fof(f832,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f831,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f830])).

fof(f830,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f795])).

fof(f795,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f720])).

fof(f720,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f857,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f829])).

fof(f829,plain,
    ( k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f794,f828])).

fof(f828,plain,
    ( ? [X0] :
        ( k2_relat_1(X0) != k9_relat_1(X0,k1_relat_1(X0))
        & v1_relat_1(X0) )
   => ( k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f794,plain,(
    ? [X0] :
      ( k2_relat_1(X0) != k9_relat_1(X0,k1_relat_1(X0))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f724])).

fof(f724,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    inference(negated_conjecture,[],[f723])).

fof(f723,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f975,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK8(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0)))
      | ~ r2_hidden(k4_tarski(X0,sK8(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0) ) ),
    inference(resolution,[],[f918,f930])).

fof(f930,plain,(
    ! [X0,X3,X1] :
      ( sQ13_eqProxy(k2_relat_1(X0),X1)
      | ~ r2_hidden(k4_tarski(X3,sK8(X0,X1)),X0)
      | ~ r2_hidden(sK8(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f888,f917])).

fof(f917,plain,(
    ! [X1,X0] :
      ( sQ13_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ13_eqProxy])])).

fof(f888,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK8(X0,X1)),X0)
      | ~ r2_hidden(sK8(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f851])).

fof(f851,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK8(X0,X1)),X0)
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0)
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK10(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f847,f850,f849,f848])).

fof(f848,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK8(X0,X1)),X0)
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK8(X0,X1)),X0)
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f849,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK8(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f850,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK10(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f847,plain,(
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
    inference(rectify,[],[f846])).

fof(f846,plain,(
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
    inference(nnf_transformation,[],[f648])).

fof(f648,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f918,plain,(
    ~ sQ13_eqProxy(k2_relat_1(sK0),k9_relat_1(sK0,k1_relat_1(sK0))) ),
    inference(equality_proxy_replacement,[],[f858,f917])).

fof(f858,plain,(
    k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f829])).

fof(f1360,plain,(
    r2_hidden(k4_tarski(sK10(sK0,sK8(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK8(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0) ),
    inference(resolution,[],[f1356,f916])).

fof(f916,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK10(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f885])).

fof(f885,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK10(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f851])).

fof(f1356,plain,(
    r2_hidden(sK8(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f1347,f1275])).

fof(f1275,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(sK0,X1))
      | r2_hidden(X0,k2_relat_1(sK0)) ) ),
    inference(resolution,[],[f942,f915])).

fof(f915,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f886])).

fof(f886,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f851])).

fof(f942,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(sK1(X2,X3,sK0),X2),sK0)
      | ~ r2_hidden(X2,k9_relat_1(sK0,X3)) ) ),
    inference(resolution,[],[f857,f860])).

fof(f860,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f833])).

fof(f1347,plain,
    ( r2_hidden(sK8(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0)))
    | r2_hidden(sK8(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k2_relat_1(sK0)) ),
    inference(resolution,[],[f974,f915])).

fof(f974,plain,
    ( r2_hidden(k4_tarski(sK9(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),sK8(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)
    | r2_hidden(sK8(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0))) ),
    inference(resolution,[],[f918,f931])).

fof(f931,plain,(
    ! [X0,X1] :
      ( sQ13_eqProxy(k2_relat_1(X0),X1)
      | r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0)
      | r2_hidden(sK8(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f887,f917])).

fof(f887,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0)
      | r2_hidden(sK8(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f851])).
%------------------------------------------------------------------------------
