%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0534+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:35 EST 2020

% Result     : Theorem 22.37s
% Output     : Refutation 22.91s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 480 expanded)
%              Number of leaves         :   19 ( 137 expanded)
%              Depth                    :   17
%              Number of atoms          :  550 (2562 expanded)
%              Number of equality atoms :   42 ( 347 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16874,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5356,f5372,f5383,f5391,f12325,f12385,f12394,f12407,f12459,f12568,f16873])).

fof(f16873,plain,
    ( ~ spl153_7
    | spl153_8
    | ~ spl153_9
    | spl153_18
    | spl153_19 ),
    inference(avatar_contradiction_clause,[],[f16870])).

fof(f16870,plain,
    ( $false
    | ~ spl153_7
    | spl153_8
    | ~ spl153_9
    | spl153_18
    | spl153_19 ),
    inference(unit_resulting_resolution,[],[f3062,f12379,f5355,f12555,f4293])).

fof(f4293,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X3,X2))
      | ~ r1_tarski(X2,X1)
      | r2_hidden(X0,X3)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f2375,f3122])).

fof(f3122,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f2671])).

fof(f2671,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1704])).

fof(f1704,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK126(X0,X1,X2),X1)
              & ~ r2_hidden(sK126(X0,X1,X2),X0) )
            | ~ r2_hidden(sK126(X0,X1,X2),X2) )
          & ( r2_hidden(sK126(X0,X1,X2),X1)
            | r2_hidden(sK126(X0,X1,X2),X0)
            | r2_hidden(sK126(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK126])],[f1702,f1703])).

fof(f1703,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK126(X0,X1,X2),X1)
            & ~ r2_hidden(sK126(X0,X1,X2),X0) )
          | ~ r2_hidden(sK126(X0,X1,X2),X2) )
        & ( r2_hidden(sK126(X0,X1,X2),X1)
          | r2_hidden(sK126(X0,X1,X2),X0)
          | r2_hidden(sK126(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1702,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f1701])).

fof(f1701,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f1700])).

fof(f1700,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f2375,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1588])).

fof(f1588,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK81(X0,X1),X1)
          & r2_hidden(sK81(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK81])],[f1586,f1587])).

fof(f1587,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK81(X0,X1),X1)
        & r2_hidden(sK81(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1586,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1585])).

fof(f1585,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1148])).

fof(f1148,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f12555,plain,
    ( ~ r2_hidden(sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK3)
    | ~ spl153_7
    | spl153_8
    | spl153_19 ),
    inference(subsumption_resolution,[],[f12554,f1810])).

fof(f1810,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f1393])).

fof(f1393,plain,
    ( k8_relat_1(k2_xboole_0(sK3,sK4),sK5) != k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f798,f1392])).

fof(f1392,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
        & v1_relat_1(X2) )
   => ( k8_relat_1(k2_xboole_0(sK3,sK4),sK5) != k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f798,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f711])).

fof(f711,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k8_relat_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f710])).

fof(f710,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_relat_1)).

fof(f12554,plain,
    ( ~ r2_hidden(sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK3)
    | ~ v1_relat_1(sK5)
    | ~ spl153_7
    | spl153_8
    | spl153_19 ),
    inference(subsumption_resolution,[],[f12552,f12506])).

fof(f12506,plain,
    ( r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | ~ spl153_7
    | spl153_8 ),
    inference(subsumption_resolution,[],[f12412,f5350])).

fof(f5350,plain,
    ( ~ r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | spl153_8 ),
    inference(avatar_component_clause,[],[f5349])).

fof(f5349,plain,
    ( spl153_8
  <=> r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_8])])).

fof(f12412,plain,
    ( r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ spl153_7 ),
    inference(subsumption_resolution,[],[f4166,f5346])).

fof(f5346,plain,
    ( v1_relat_1(k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ spl153_7 ),
    inference(avatar_component_clause,[],[f5345])).

fof(f5345,plain,
    ( spl153_7
  <=> v1_relat_1(k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_7])])).

fof(f4166,plain,
    ( r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ v1_relat_1(k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))) ),
    inference(subsumption_resolution,[],[f4165,f1810])).

fof(f4165,plain,
    ( r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ v1_relat_1(k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f3413,f3255])).

fof(f3255,plain,(
    ~ sQ152_eqProxy(k8_relat_1(k2_xboole_0(sK3,sK4),sK5),k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))) ),
    inference(equality_proxy_replacement,[],[f1811,f3237])).

fof(f3237,plain,(
    ! [X1,X0] :
      ( sQ152_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ152_eqProxy])])).

fof(f1811,plain,(
    k8_relat_1(k2_xboole_0(sK3,sK4),sK5) != k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f1393])).

fof(f3413,plain,(
    ! [X2,X0,X1] :
      ( sQ152_eqProxy(k8_relat_1(X0,X1),X2)
      | r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f2149,f3237])).

fof(f2149,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1489])).

fof(f1489,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK50(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X1)
                    & r2_hidden(sK50(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK49,sK50])],[f1487,f1488])).

fof(f1488,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X1)
          | ~ r2_hidden(sK50(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X1)
            & r2_hidden(sK50(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1487,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f1486])).

fof(f1486,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1485])).

fof(f1485,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f958])).

fof(f958,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f642])).

fof(f642,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

fof(f12552,plain,
    ( ~ r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | ~ r2_hidden(sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK3)
    | ~ v1_relat_1(sK5)
    | spl153_19 ),
    inference(resolution,[],[f12383,f4157])).

fof(f4157,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f3053,f2099])).

fof(f2099,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f909])).

fof(f909,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f658])).

fof(f658,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f3053,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f2147])).

fof(f2147,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1489])).

fof(f12383,plain,
    ( ~ r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k8_relat_1(sK3,sK5))
    | spl153_19 ),
    inference(avatar_component_clause,[],[f12382])).

fof(f12382,plain,
    ( spl153_19
  <=> r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k8_relat_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_19])])).

fof(f5355,plain,
    ( r2_hidden(sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),k2_xboole_0(sK3,sK4))
    | ~ spl153_9 ),
    inference(avatar_component_clause,[],[f5353])).

fof(f5353,plain,
    ( spl153_9
  <=> r2_hidden(sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),k2_xboole_0(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_9])])).

fof(f12379,plain,
    ( ~ r2_hidden(sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK4)
    | spl153_18 ),
    inference(avatar_component_clause,[],[f12378])).

fof(f12378,plain,
    ( spl153_18
  <=> r2_hidden(sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_18])])).

fof(f3062,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f2353])).

fof(f2353,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1567])).

fof(f1567,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1566])).

fof(f1566,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f12568,plain,
    ( ~ spl153_7
    | spl153_8
    | ~ spl153_18 ),
    inference(avatar_contradiction_clause,[],[f12567])).

fof(f12567,plain,
    ( $false
    | ~ spl153_7
    | spl153_8
    | ~ spl153_18 ),
    inference(subsumption_resolution,[],[f12566,f1810])).

fof(f12566,plain,
    ( ~ v1_relat_1(sK5)
    | ~ spl153_7
    | spl153_8
    | ~ spl153_18 ),
    inference(subsumption_resolution,[],[f12565,f12380])).

fof(f12380,plain,
    ( r2_hidden(sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK4)
    | ~ spl153_18 ),
    inference(avatar_component_clause,[],[f12378])).

fof(f12565,plain,
    ( ~ r2_hidden(sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK4)
    | ~ v1_relat_1(sK5)
    | ~ spl153_7
    | spl153_8 ),
    inference(subsumption_resolution,[],[f12562,f12506])).

fof(f12562,plain,
    ( ~ r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | ~ r2_hidden(sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK4)
    | ~ v1_relat_1(sK5)
    | spl153_8 ),
    inference(resolution,[],[f12436,f4157])).

fof(f12436,plain,
    ( ~ r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k8_relat_1(sK4,sK5))
    | spl153_8 ),
    inference(resolution,[],[f5350,f3120])).

fof(f3120,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f2673])).

fof(f2673,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1704])).

fof(f12459,plain,
    ( spl153_8
    | ~ spl153_19 ),
    inference(avatar_contradiction_clause,[],[f12458])).

fof(f12458,plain,
    ( $false
    | spl153_8
    | ~ spl153_19 ),
    inference(subsumption_resolution,[],[f12435,f12384])).

fof(f12384,plain,
    ( r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k8_relat_1(sK3,sK5))
    | ~ spl153_19 ),
    inference(avatar_component_clause,[],[f12382])).

fof(f12435,plain,
    ( ~ r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k8_relat_1(sK3,sK5))
    | spl153_8 ),
    inference(resolution,[],[f5350,f3121])).

fof(f3121,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f2672])).

fof(f2672,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1704])).

fof(f12407,plain,
    ( ~ spl153_7
    | ~ spl153_8
    | ~ spl153_9
    | ~ spl153_19 ),
    inference(avatar_contradiction_clause,[],[f12406])).

fof(f12406,plain,
    ( $false
    | ~ spl153_7
    | ~ spl153_8
    | ~ spl153_9
    | ~ spl153_19 ),
    inference(subsumption_resolution,[],[f12405,f1810])).

fof(f12405,plain,
    ( ~ v1_relat_1(sK5)
    | ~ spl153_7
    | ~ spl153_8
    | ~ spl153_9
    | ~ spl153_19 ),
    inference(subsumption_resolution,[],[f12397,f12340])).

fof(f12340,plain,
    ( ~ r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | ~ spl153_7
    | ~ spl153_8
    | ~ spl153_9 ),
    inference(subsumption_resolution,[],[f12327,f5355])).

fof(f12327,plain,
    ( ~ r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | ~ r2_hidden(sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),k2_xboole_0(sK3,sK4))
    | ~ spl153_7
    | ~ spl153_8 ),
    inference(subsumption_resolution,[],[f12326,f5346])).

fof(f12326,plain,
    ( ~ r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | ~ r2_hidden(sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),k2_xboole_0(sK3,sK4))
    | ~ v1_relat_1(k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ spl153_8 ),
    inference(subsumption_resolution,[],[f4168,f5351])).

fof(f5351,plain,
    ( r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ spl153_8 ),
    inference(avatar_component_clause,[],[f5349])).

fof(f4168,plain,
    ( ~ r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | ~ r2_hidden(sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),k2_xboole_0(sK3,sK4))
    | ~ r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ v1_relat_1(k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))) ),
    inference(subsumption_resolution,[],[f4167,f1810])).

fof(f4167,plain,
    ( ~ r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | ~ r2_hidden(sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),k2_xboole_0(sK3,sK4))
    | ~ r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ v1_relat_1(k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f3412,f3255])).

fof(f3412,plain,(
    ! [X2,X0,X1] :
      ( sQ152_eqProxy(k8_relat_1(X0,X1),X2)
      | ~ r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X1)
      | ~ r2_hidden(sK50(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f2150,f3237])).

fof(f2150,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X1)
      | ~ r2_hidden(sK50(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1489])).

fof(f12397,plain,
    ( r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl153_19 ),
    inference(resolution,[],[f12384,f4155])).

fof(f4155,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X5,X6),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f3054,f2099])).

fof(f3054,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f2146])).

fof(f2146,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1489])).

fof(f12394,plain,
    ( ~ spl153_7
    | ~ spl153_8
    | ~ spl153_9
    | spl153_19 ),
    inference(avatar_contradiction_clause,[],[f12391])).

fof(f12391,plain,
    ( $false
    | ~ spl153_7
    | ~ spl153_8
    | ~ spl153_9
    | spl153_19 ),
    inference(unit_resulting_resolution,[],[f1810,f12340,f5351,f12383,f4156])).

fof(f4156,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_xboole_0(X3,k8_relat_1(X4,X2)))
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,X1),X3)
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(resolution,[],[f4155,f3122])).

fof(f12385,plain,
    ( spl153_18
    | spl153_19
    | ~ spl153_8 ),
    inference(avatar_split_clause,[],[f5398,f5349,f12382,f12378])).

fof(f5398,plain,
    ( r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k8_relat_1(sK3,sK5))
    | r2_hidden(sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK4)
    | ~ spl153_8 ),
    inference(subsumption_resolution,[],[f5393,f1810])).

fof(f5393,plain,
    ( ~ v1_relat_1(sK5)
    | r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k8_relat_1(sK3,sK5))
    | r2_hidden(sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK4)
    | ~ spl153_8 ),
    inference(resolution,[],[f5351,f4154])).

fof(f4154,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X0),k2_xboole_0(X4,k8_relat_1(X1,X2)))
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,X0),X4)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f4153,f3122])).

fof(f4153,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | r2_hidden(X6,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f3055,f2099])).

fof(f3055,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f2145])).

fof(f2145,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1489])).

fof(f12325,plain,
    ( ~ spl153_8
    | spl153_9 ),
    inference(avatar_contradiction_clause,[],[f12324])).

fof(f12324,plain,
    ( $false
    | ~ spl153_8
    | spl153_9 ),
    inference(subsumption_resolution,[],[f12323,f1810])).

fof(f12323,plain,
    ( ~ v1_relat_1(sK5)
    | ~ spl153_8
    | spl153_9 ),
    inference(subsumption_resolution,[],[f12315,f5361])).

fof(f5361,plain,
    ( ~ r2_hidden(sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK3)
    | spl153_9 ),
    inference(resolution,[],[f5354,f3121])).

fof(f5354,plain,
    ( ~ r2_hidden(sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),k2_xboole_0(sK3,sK4))
    | spl153_9 ),
    inference(avatar_component_clause,[],[f5353])).

fof(f12315,plain,
    ( r2_hidden(sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK3)
    | ~ v1_relat_1(sK5)
    | ~ spl153_8
    | spl153_9 ),
    inference(resolution,[],[f12309,f4153])).

fof(f12309,plain,
    ( r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k8_relat_1(sK3,sK5))
    | ~ spl153_8
    | spl153_9 ),
    inference(subsumption_resolution,[],[f5398,f5362])).

fof(f5362,plain,
    ( ~ r2_hidden(sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK4)
    | spl153_9 ),
    inference(resolution,[],[f5354,f3120])).

fof(f5391,plain,(
    spl153_11 ),
    inference(avatar_contradiction_clause,[],[f5390])).

fof(f5390,plain,
    ( $false
    | spl153_11 ),
    inference(subsumption_resolution,[],[f5385,f1810])).

fof(f5385,plain,
    ( ~ v1_relat_1(sK5)
    | spl153_11 ),
    inference(resolution,[],[f5371,f2099])).

fof(f5371,plain,
    ( ~ v1_relat_1(k8_relat_1(sK4,sK5))
    | spl153_11 ),
    inference(avatar_component_clause,[],[f5369])).

fof(f5369,plain,
    ( spl153_11
  <=> v1_relat_1(k8_relat_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_11])])).

fof(f5383,plain,(
    spl153_10 ),
    inference(avatar_contradiction_clause,[],[f5382])).

fof(f5382,plain,
    ( $false
    | spl153_10 ),
    inference(subsumption_resolution,[],[f5377,f1810])).

fof(f5377,plain,
    ( ~ v1_relat_1(sK5)
    | spl153_10 ),
    inference(resolution,[],[f5367,f2099])).

fof(f5367,plain,
    ( ~ v1_relat_1(k8_relat_1(sK3,sK5))
    | spl153_10 ),
    inference(avatar_component_clause,[],[f5365])).

fof(f5365,plain,
    ( spl153_10
  <=> v1_relat_1(k8_relat_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_10])])).

fof(f5372,plain,
    ( ~ spl153_10
    | ~ spl153_11
    | spl153_7 ),
    inference(avatar_split_clause,[],[f5357,f5345,f5369,f5365])).

fof(f5357,plain,
    ( ~ v1_relat_1(k8_relat_1(sK4,sK5))
    | ~ v1_relat_1(k8_relat_1(sK3,sK5))
    | spl153_7 ),
    inference(resolution,[],[f5347,f2316])).

fof(f2316,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1123])).

fof(f1123,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1122])).

fof(f1122,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f670])).

fof(f670,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_relat_1)).

fof(f5347,plain,
    ( ~ v1_relat_1(k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | spl153_7 ),
    inference(avatar_component_clause,[],[f5345])).

fof(f5356,plain,
    ( ~ spl153_7
    | spl153_8
    | spl153_9 ),
    inference(avatar_split_clause,[],[f4164,f5353,f5349,f5345])).

fof(f4164,plain,
    ( r2_hidden(sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),k2_xboole_0(sK3,sK4))
    | r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ v1_relat_1(k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))) ),
    inference(subsumption_resolution,[],[f4163,f1810])).

fof(f4163,plain,
    ( r2_hidden(sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),k2_xboole_0(sK3,sK4))
    | r2_hidden(k4_tarski(sK49(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k2_xboole_0(sK3,sK4),sK5,k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ v1_relat_1(k2_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f3414,f3255])).

fof(f3414,plain,(
    ! [X2,X0,X1] :
      ( sQ152_eqProxy(k8_relat_1(X0,X1),X2)
      | r2_hidden(sK50(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f2148,f3237])).

fof(f2148,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(sK50(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1489])).
%------------------------------------------------------------------------------
