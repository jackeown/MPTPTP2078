%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0453+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:31 EST 2020

% Result     : Theorem 18.74s
% Output     : Refutation 18.74s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 270 expanded)
%              Number of leaves         :   18 (  89 expanded)
%              Depth                    :   12
%              Number of atoms          :  367 (1290 expanded)
%              Number of equality atoms :   34 ( 184 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13729,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5856,f5863,f5876,f5886,f12818,f12820,f12837,f12924,f13694,f13702,f13725,f13728])).

fof(f13728,plain,
    ( ~ spl135_6
    | spl135_14 ),
    inference(avatar_contradiction_clause,[],[f13727])).

fof(f13727,plain,
    ( $false
    | ~ spl135_6
    | spl135_14 ),
    inference(unit_resulting_resolution,[],[f5854,f12817,f2689])).

fof(f2689,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f2258])).

fof(f2258,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1435])).

fof(f1435,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK108(X0,X1,X2),X1)
            | ~ r2_hidden(sK108(X0,X1,X2),X0)
            | ~ r2_hidden(sK108(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK108(X0,X1,X2),X1)
              & r2_hidden(sK108(X0,X1,X2),X0) )
            | r2_hidden(sK108(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK108])],[f1433,f1434])).

fof(f1434,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK108(X0,X1,X2),X1)
          | ~ r2_hidden(sK108(X0,X1,X2),X0)
          | ~ r2_hidden(sK108(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK108(X0,X1,X2),X1)
            & r2_hidden(sK108(X0,X1,X2),X0) )
          | r2_hidden(sK108(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1433,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f1432])).

fof(f1432,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f1431])).

fof(f1431,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f12817,plain,
    ( ~ r2_hidden(k4_tarski(sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),sK4)
    | spl135_14 ),
    inference(avatar_component_clause,[],[f12815])).

fof(f12815,plain,
    ( spl135_14
  <=> r2_hidden(k4_tarski(sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl135_14])])).

fof(f5854,plain,
    ( r2_hidden(k4_tarski(sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),k3_xboole_0(sK3,sK4))
    | ~ spl135_6 ),
    inference(avatar_component_clause,[],[f5853])).

fof(f5853,plain,
    ( spl135_6
  <=> r2_hidden(k4_tarski(sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),k3_xboole_0(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl135_6])])).

fof(f13725,plain,
    ( ~ spl135_14
    | spl135_16 ),
    inference(avatar_contradiction_clause,[],[f13724])).

fof(f13724,plain,
    ( $false
    | ~ spl135_14
    | spl135_16 ),
    inference(subsumption_resolution,[],[f13723,f1541])).

fof(f1541,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f1165])).

fof(f1165,plain,
    ( k4_relat_1(k3_xboole_0(sK3,sK4)) != k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))
    & v1_relat_1(sK4)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f696,f1164,f1163])).

fof(f1163,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k4_relat_1(k3_xboole_0(X0,X1)) != k3_xboole_0(k4_relat_1(X0),k4_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k4_relat_1(k3_xboole_0(sK3,X1)) != k3_xboole_0(k4_relat_1(sK3),k4_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f1164,plain,
    ( ? [X1] :
        ( k4_relat_1(k3_xboole_0(sK3,X1)) != k3_xboole_0(k4_relat_1(sK3),k4_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k4_relat_1(k3_xboole_0(sK3,sK4)) != k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f696,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_relat_1(k3_xboole_0(X0,X1)) != k3_xboole_0(k4_relat_1(X0),k4_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f679])).

fof(f679,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k4_relat_1(k3_xboole_0(X0,X1)) = k3_xboole_0(k4_relat_1(X0),k4_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f678])).

fof(f678,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k3_xboole_0(X0,X1)) = k3_xboole_0(k4_relat_1(X0),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relat_1)).

fof(f13723,plain,
    ( ~ v1_relat_1(sK4)
    | ~ spl135_14
    | spl135_16 ),
    inference(subsumption_resolution,[],[f13720,f12816])).

fof(f12816,plain,
    ( r2_hidden(k4_tarski(sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),sK4)
    | ~ spl135_14 ),
    inference(avatar_component_clause,[],[f12815])).

fof(f13720,plain,
    ( ~ r2_hidden(k4_tarski(sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),sK4)
    | ~ v1_relat_1(sK4)
    | spl135_16 ),
    inference(resolution,[],[f13693,f3624])).

fof(f3624,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f2617,f1607])).

fof(f1607,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f711])).

fof(f711,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f649])).

fof(f649,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f2617,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1631])).

fof(f1631,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1181])).

fof(f1181,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK12(X0,X1),sK11(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK11(X0,X1),sK12(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK12(X0,X1),sK11(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK11(X0,X1),sK12(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f1179,f1180])).

fof(f1180,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK12(X0,X1),sK11(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK11(X0,X1),sK12(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK12(X0,X1),sK11(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK11(X0,X1),sK12(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1179,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1178])).

fof(f1178,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f731])).

fof(f731,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f645])).

fof(f645,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

fof(f13693,plain,
    ( ~ r2_hidden(k4_tarski(sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),k4_relat_1(sK4))
    | spl135_16 ),
    inference(avatar_component_clause,[],[f13691])).

fof(f13691,plain,
    ( spl135_16
  <=> r2_hidden(k4_tarski(sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),k4_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl135_16])])).

fof(f13702,plain,
    ( ~ spl135_13
    | spl135_15 ),
    inference(avatar_contradiction_clause,[],[f13701])).

fof(f13701,plain,
    ( $false
    | ~ spl135_13
    | spl135_15 ),
    inference(subsumption_resolution,[],[f13700,f1540])).

fof(f1540,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f1165])).

fof(f13700,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl135_13
    | spl135_15 ),
    inference(subsumption_resolution,[],[f13697,f12812])).

fof(f12812,plain,
    ( r2_hidden(k4_tarski(sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),sK3)
    | ~ spl135_13 ),
    inference(avatar_component_clause,[],[f12811])).

fof(f12811,plain,
    ( spl135_13
  <=> r2_hidden(k4_tarski(sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl135_13])])).

fof(f13697,plain,
    ( ~ r2_hidden(k4_tarski(sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),sK3)
    | ~ v1_relat_1(sK3)
    | spl135_15 ),
    inference(resolution,[],[f13689,f3624])).

fof(f13689,plain,
    ( ~ r2_hidden(k4_tarski(sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),k4_relat_1(sK3))
    | spl135_15 ),
    inference(avatar_component_clause,[],[f13687])).

fof(f13687,plain,
    ( spl135_15
  <=> r2_hidden(k4_tarski(sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),k4_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl135_15])])).

fof(f13694,plain,
    ( ~ spl135_15
    | ~ spl135_16
    | spl135_5 ),
    inference(avatar_split_clause,[],[f12956,f5849,f13691,f13687])).

fof(f5849,plain,
    ( spl135_5
  <=> r2_hidden(k4_tarski(sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl135_5])])).

fof(f12956,plain,
    ( ~ r2_hidden(k4_tarski(sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),k4_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),k4_relat_1(sK3))
    | spl135_5 ),
    inference(resolution,[],[f5851,f2688])).

fof(f2688,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f2259])).

fof(f2259,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1435])).

fof(f5851,plain,
    ( ~ r2_hidden(k4_tarski(sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))
    | spl135_5 ),
    inference(avatar_component_clause,[],[f5849])).

fof(f12924,plain,
    ( ~ spl135_5
    | spl135_14 ),
    inference(avatar_contradiction_clause,[],[f12923])).

fof(f12923,plain,
    ( $false
    | ~ spl135_5
    | spl135_14 ),
    inference(subsumption_resolution,[],[f12922,f1541])).

fof(f12922,plain,
    ( ~ v1_relat_1(sK4)
    | ~ spl135_5
    | spl135_14 ),
    inference(subsumption_resolution,[],[f12915,f12817])).

fof(f12915,plain,
    ( r2_hidden(k4_tarski(sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl135_5 ),
    inference(resolution,[],[f12866,f3626])).

fof(f3626,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f2618,f1607])).

fof(f2618,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1630])).

fof(f1630,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1181])).

fof(f12866,plain,
    ( r2_hidden(k4_tarski(sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),k4_relat_1(sK4))
    | ~ spl135_5 ),
    inference(resolution,[],[f5850,f2689])).

fof(f5850,plain,
    ( r2_hidden(k4_tarski(sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))
    | ~ spl135_5 ),
    inference(avatar_component_clause,[],[f5849])).

fof(f12837,plain,
    ( ~ spl135_6
    | spl135_13 ),
    inference(avatar_contradiction_clause,[],[f12836])).

fof(f12836,plain,
    ( $false
    | ~ spl135_6
    | spl135_13 ),
    inference(subsumption_resolution,[],[f12829,f12813])).

fof(f12813,plain,
    ( ~ r2_hidden(k4_tarski(sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),sK3)
    | spl135_13 ),
    inference(avatar_component_clause,[],[f12811])).

fof(f12829,plain,
    ( r2_hidden(k4_tarski(sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),sK3)
    | ~ spl135_6 ),
    inference(resolution,[],[f5854,f2690])).

fof(f2690,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f2257])).

fof(f2257,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1435])).

fof(f12820,plain,
    ( ~ spl135_5
    | spl135_13 ),
    inference(avatar_contradiction_clause,[],[f12819])).

fof(f12819,plain,
    ( $false
    | ~ spl135_5
    | spl135_13 ),
    inference(unit_resulting_resolution,[],[f1540,f5888,f12813,f3626])).

fof(f5888,plain,
    ( r2_hidden(k4_tarski(sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),k4_relat_1(sK3))
    | ~ spl135_5 ),
    inference(resolution,[],[f5850,f2690])).

fof(f12818,plain,
    ( ~ spl135_13
    | ~ spl135_14
    | spl135_6 ),
    inference(avatar_split_clause,[],[f5869,f5853,f12815,f12811])).

fof(f5869,plain,
    ( ~ r2_hidden(k4_tarski(sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),sK4)
    | ~ r2_hidden(k4_tarski(sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),sK3)
    | spl135_6 ),
    inference(resolution,[],[f5855,f2688])).

fof(f5855,plain,
    ( ~ r2_hidden(k4_tarski(sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),k3_xboole_0(sK3,sK4))
    | spl135_6 ),
    inference(avatar_component_clause,[],[f5853])).

fof(f5886,plain,
    ( ~ spl135_3
    | ~ spl135_4
    | spl135_5
    | spl135_6 ),
    inference(avatar_contradiction_clause,[],[f5884])).

fof(f5884,plain,
    ( $false
    | ~ spl135_3
    | ~ spl135_4
    | spl135_5
    | spl135_6 ),
    inference(unit_resulting_resolution,[],[f5842,f5846,f2826,f5855,f5851,f2860])).

fof(f2860,plain,(
    ! [X0,X1] :
      ( sQ134_eqProxy(k4_relat_1(X0),X1)
      | r2_hidden(k4_tarski(sK12(X0,X1),sK11(X0,X1)),X0)
      | r2_hidden(k4_tarski(sK11(X0,X1),sK12(X0,X1)),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f1632,f2808])).

fof(f2808,plain,(
    ! [X1,X0] :
      ( sQ134_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ134_eqProxy])])).

fof(f1632,plain,(
    ! [X0,X1] :
      ( k4_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK12(X0,X1),sK11(X0,X1)),X0)
      | r2_hidden(k4_tarski(sK11(X0,X1),sK12(X0,X1)),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1181])).

fof(f2826,plain,(
    ~ sQ134_eqProxy(k4_relat_1(k3_xboole_0(sK3,sK4)),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))) ),
    inference(equality_proxy_replacement,[],[f1542,f2808])).

fof(f1542,plain,(
    k4_relat_1(k3_xboole_0(sK3,sK4)) != k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f1165])).

fof(f5846,plain,
    ( v1_relat_1(k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))
    | ~ spl135_4 ),
    inference(avatar_component_clause,[],[f5845])).

fof(f5845,plain,
    ( spl135_4
  <=> v1_relat_1(k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl135_4])])).

fof(f5842,plain,
    ( v1_relat_1(k3_xboole_0(sK3,sK4))
    | ~ spl135_3 ),
    inference(avatar_component_clause,[],[f5841])).

fof(f5841,plain,
    ( spl135_3
  <=> v1_relat_1(k3_xboole_0(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl135_3])])).

fof(f5876,plain,(
    spl135_4 ),
    inference(avatar_contradiction_clause,[],[f5875])).

fof(f5875,plain,
    ( $false
    | spl135_4 ),
    inference(subsumption_resolution,[],[f5871,f1540])).

fof(f5871,plain,
    ( ~ v1_relat_1(sK3)
    | spl135_4 ),
    inference(resolution,[],[f5866,f1607])).

fof(f5866,plain,
    ( ~ v1_relat_1(k4_relat_1(sK3))
    | spl135_4 ),
    inference(resolution,[],[f5847,f1771])).

fof(f1771,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f764])).

fof(f764,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f650])).

fof(f650,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f5847,plain,
    ( ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))
    | spl135_4 ),
    inference(avatar_component_clause,[],[f5845])).

fof(f5863,plain,(
    spl135_3 ),
    inference(avatar_contradiction_clause,[],[f5862])).

fof(f5862,plain,
    ( $false
    | spl135_3 ),
    inference(subsumption_resolution,[],[f5858,f1540])).

fof(f5858,plain,
    ( ~ v1_relat_1(sK3)
    | spl135_3 ),
    inference(resolution,[],[f5843,f1771])).

fof(f5843,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK3,sK4))
    | spl135_3 ),
    inference(avatar_component_clause,[],[f5841])).

fof(f5856,plain,
    ( ~ spl135_3
    | ~ spl135_4
    | ~ spl135_5
    | ~ spl135_6 ),
    inference(avatar_split_clause,[],[f3631,f5853,f5849,f5845,f5841])).

fof(f3631,plain,
    ( ~ r2_hidden(k4_tarski(sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),k3_xboole_0(sK3,sK4))
    | ~ r2_hidden(k4_tarski(sK11(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4))),sK12(k3_xboole_0(sK3,sK4),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))),k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))
    | ~ v1_relat_1(k3_xboole_0(k4_relat_1(sK3),k4_relat_1(sK4)))
    | ~ v1_relat_1(k3_xboole_0(sK3,sK4)) ),
    inference(resolution,[],[f2859,f2826])).

fof(f2859,plain,(
    ! [X0,X1] :
      ( sQ134_eqProxy(k4_relat_1(X0),X1)
      | ~ r2_hidden(k4_tarski(sK12(X0,X1),sK11(X0,X1)),X0)
      | ~ r2_hidden(k4_tarski(sK11(X0,X1),sK12(X0,X1)),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f1633,f2808])).

fof(f1633,plain,(
    ! [X0,X1] :
      ( k4_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK12(X0,X1),sK11(X0,X1)),X0)
      | ~ r2_hidden(k4_tarski(sK11(X0,X1),sK12(X0,X1)),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1181])).
%------------------------------------------------------------------------------
