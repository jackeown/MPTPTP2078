%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0468+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:31 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   26 (  39 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 120 expanded)
%              Number of equality atoms :   12 (  27 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1054,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1032,f1022])).

fof(f1022,plain,(
    ! [X3] : r1_tarski(sK0,X3) ),
    inference(subsumption_resolution,[],[f1010,f814])).

fof(f814,plain,(
    ! [X2,X1] : ~ r2_hidden(k4_tarski(X1,X2),sK0) ),
    inference(cnf_transformation,[],[f740])).

fof(f740,plain,
    ( k1_xboole_0 != sK0
    & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f703,f739])).

fof(f739,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != sK0
      & ! [X2,X1] : ~ r2_hidden(k4_tarski(X1,X2),sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f703,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f702])).

fof(f702,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f699])).

fof(f699,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
         => k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f698])).

fof(f698,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

fof(f1010,plain,(
    ! [X3] :
      ( r1_tarski(sK0,X3)
      | r2_hidden(k4_tarski(sK33(sK0,X3),sK34(sK0,X3)),sK0) ) ),
    inference(resolution,[],[f813,f916])).

fof(f916,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK33(X0,X1),sK34(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f808])).

fof(f808,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK33(X0,X1),sK34(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK33(X0,X1),sK34(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK33,sK34])],[f806,f807])).

fof(f807,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK33(X0,X1),sK34(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK33(X0,X1),sK34(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f806,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f805])).

fof(f805,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f732])).

fof(f732,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f642])).

fof(f642,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(f813,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f740])).

fof(f1032,plain,(
    ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(resolution,[],[f943,f965])).

fof(f965,plain,(
    ! [X0] :
      ( sQ37_eqProxy(k1_xboole_0,X0)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(equality_proxy_replacement,[],[f841,f942])).

fof(f942,plain,(
    ! [X1,X0] :
      ( sQ37_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ37_eqProxy])])).

fof(f841,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f714])).

fof(f714,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f101,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f943,plain,(
    ~ sQ37_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f815,f942])).

fof(f815,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f740])).
%------------------------------------------------------------------------------
