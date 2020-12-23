%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : setfam_1__t10_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:12 EDT 2019

% Result     : Theorem 74.23s
% Output     : Refutation 74.23s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 240 expanded)
%              Number of leaves         :   27 (  81 expanded)
%              Depth                    :   12
%              Number of atoms          :  475 (1248 expanded)
%              Number of equality atoms :  104 ( 403 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25637,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f288,f783,f1083,f1085,f1093,f4424,f25625])).

fof(f25625,plain,
    ( spl10_1
    | spl10_9
    | ~ spl10_10
    | ~ spl10_22 ),
    inference(avatar_contradiction_clause,[],[f25624])).

fof(f25624,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f25611,f8512])).

fof(f8512,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(sK0,sK1),sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1)))),sK1)
    | ~ spl10_1
    | ~ spl10_9
    | ~ spl10_22 ),
    inference(unit_resulting_resolution,[],[f83,f779,f4549,f139])).

fof(f139,plain,(
    ! [X0,X7,X5] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X0,X7,X5,X1] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK3(X0,X1),sK4(X0,X1))
                  & r2_hidden(sK4(X0,X1),X0) )
                | ~ r2_hidden(sK3(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK3(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK3(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK5(X0,X5))
                    & r2_hidden(sK5(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f60,f63,f62,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK3(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK3(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK5(X0,X5))
        & r2_hidden(sK5(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t10_setfam_1.p',d1_setfam_1)).

fof(f4549,plain,
    ( ~ r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),sK5(k2_xboole_0(sK0,sK1),sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1)))))
    | ~ spl10_1
    | ~ spl10_9 ),
    inference(unit_resulting_resolution,[],[f260,f278,f137])).

fof(f137,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | ~ r2_hidden(X5,sK5(X0,X5))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK5(X0,X5))
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f278,plain,
    ( ~ r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(k2_xboole_0(sK0,sK1)))
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl10_9
  <=> ~ r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f260,plain,
    ( k1_xboole_0 != k2_xboole_0(sK0,sK1)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl10_1
  <=> k1_xboole_0 != k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f779,plain,
    ( r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK1))
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f778])).

fof(f778,plain,
    ( spl10_22
  <=> r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f83,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
    ( k1_setfam_1(k2_xboole_0(sK0,sK1)) != k3_xboole_0(k1_setfam_1(sK0),k1_setfam_1(sK1))
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f55])).

fof(f55,plain,
    ( ? [X0,X1] :
        ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( k1_setfam_1(k2_xboole_0(sK0,sK1)) != k3_xboole_0(k1_setfam_1(sK0),k1_setfam_1(sK1))
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t10_setfam_1.p',t10_setfam_1)).

fof(f25611,plain,
    ( r2_hidden(sK5(k2_xboole_0(sK0,sK1),sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1)))),sK1)
    | ~ spl10_1
    | ~ spl10_9
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f4548,f8511,f147])).

fof(f147,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f126])).

fof(f126,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
              & ~ r2_hidden(sK8(X0,X1,X2),X0) )
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( r2_hidden(sK8(X0,X1,X2),X1)
            | r2_hidden(sK8(X0,X1,X2),X0)
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f79,f80])).

fof(f80,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
            & ~ r2_hidden(sK8(X0,X1,X2),X0) )
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( r2_hidden(sK8(X0,X1,X2),X1)
          | r2_hidden(sK8(X0,X1,X2),X0)
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
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
    inference(rectify,[],[f78])).

fof(f78,plain,(
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
    inference(flattening,[],[f77])).

fof(f77,plain,(
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
    file('/export/starexec/sandbox2/benchmark/setfam_1__t10_setfam_1.p',d3_xboole_0)).

fof(f8511,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(sK0,sK1),sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1)))),sK0)
    | ~ spl10_1
    | ~ spl10_9
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f82,f287,f4549,f139])).

fof(f287,plain,
    ( r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK0))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f286])).

fof(f286,plain,
    ( spl10_10
  <=> r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f82,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f56])).

fof(f4548,plain,
    ( r2_hidden(sK5(k2_xboole_0(sK0,sK1),sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1)))),k2_xboole_0(sK0,sK1))
    | ~ spl10_1
    | ~ spl10_9 ),
    inference(unit_resulting_resolution,[],[f260,f278,f138])).

fof(f138,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | r2_hidden(sK5(X0,X5),X0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK5(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f4424,plain,(
    ~ spl10_0 ),
    inference(avatar_contradiction_clause,[],[f4407])).

fof(f4407,plain,
    ( $false
    | ~ spl10_0 ),
    inference(unit_resulting_resolution,[],[f85,f4145])).

fof(f4145,plain,
    ( ! [X1] : ~ v1_xboole_0(X1)
    | ~ spl10_0 ),
    inference(forward_demodulation,[],[f4126,f86])).

fof(f86,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t10_setfam_1.p',t1_boole)).

fof(f4126,plain,
    ( ! [X1] : ~ v1_xboole_0(k2_xboole_0(X1,k1_xboole_0))
    | ~ spl10_0 ),
    inference(superposition,[],[f480,f263])).

fof(f263,plain,
    ( k1_xboole_0 = k2_xboole_0(sK0,sK1)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl10_0
  <=> k1_xboole_0 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f480,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK1))) ),
    inference(unit_resulting_resolution,[],[f176,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t10_setfam_1.p',fc5_xboole_0)).

fof(f176,plain,(
    ! [X0] : ~ v1_xboole_0(k2_xboole_0(X0,sK1)) ),
    inference(unit_resulting_resolution,[],[f156,f103])).

fof(f156,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(unit_resulting_resolution,[],[f83,f88])).

fof(f88,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t10_setfam_1.p',t6_boole)).

fof(f85,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t10_setfam_1.p',dt_o_0_0_xboole_0)).

fof(f1093,plain,
    ( spl10_22
    | spl10_9 ),
    inference(avatar_split_clause,[],[f1092,f277,f778])).

fof(f1092,plain,
    ( r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK1))
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f765,f278])).

fof(f765,plain,
    ( r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK1))
    | r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(k2_xboole_0(sK0,sK1))) ),
    inference(equality_resolution,[],[f167])).

fof(f167,plain,(
    ! [X1] :
      ( k1_setfam_1(k2_xboole_0(sK0,sK1)) != X1
      | r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),X1),k1_setfam_1(sK1))
      | r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),X1),X1) ) ),
    inference(superposition,[],[f84,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK7(X0,X1,X2),X1)
      | r2_hidden(sK7(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK7(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f74,f75])).

fof(f75,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(sK7(X0,X1,X2),X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
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
    inference(rectify,[],[f73])).

fof(f73,plain,(
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
    inference(flattening,[],[f72])).

fof(f72,plain,(
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
    file('/export/starexec/sandbox2/benchmark/setfam_1__t10_setfam_1.p',d4_xboole_0)).

fof(f84,plain,(
    k1_setfam_1(k2_xboole_0(sK0,sK1)) != k3_xboole_0(k1_setfam_1(sK0),k1_setfam_1(sK1)) ),
    inference(cnf_transformation,[],[f56])).

fof(f1085,plain,
    ( ~ spl10_8
    | spl10_23 ),
    inference(avatar_contradiction_clause,[],[f1084])).

fof(f1084,plain,
    ( $false
    | ~ spl10_8
    | ~ spl10_23 ),
    inference(subsumption_resolution,[],[f1035,f782])).

fof(f782,plain,
    ( ~ r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK1))
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f781])).

fof(f781,plain,
    ( spl10_23
  <=> ~ r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f1035,plain,
    ( r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK1))
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f221,f281,f111])).

fof(f111,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f68,f69])).

fof(f69,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox2/benchmark/setfam_1__t10_setfam_1.p',d3_tarski)).

fof(f281,plain,
    ( r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(k2_xboole_0(sK0,sK1)))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl10_8
  <=> r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f221,plain,(
    ! [X6] : r1_tarski(k1_setfam_1(k2_xboole_0(X6,sK1)),k1_setfam_1(sK1)) ),
    inference(superposition,[],[f157,f94])).

fof(f94,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t10_setfam_1.p',commutativity_k2_xboole_0)).

fof(f157,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(k2_xboole_0(sK1,X0)),k1_setfam_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f92,f83,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t10_setfam_1.p',t7_setfam_1)).

fof(f92,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t10_setfam_1.p',t7_xboole_1)).

fof(f1083,plain,
    ( spl10_10
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f1036,f280,f286])).

fof(f1036,plain,
    ( r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK0))
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f151,f281,f111])).

fof(f151,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(k2_xboole_0(sK0,X0)),k1_setfam_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f92,f82,f107])).

fof(f783,plain,
    ( ~ spl10_11
    | ~ spl10_23
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f776,f280,f781,f283])).

fof(f283,plain,
    ( spl10_11
  <=> ~ r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f776,plain,
    ( ~ r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK1))
    | ~ r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK0))
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f772,f281])).

fof(f772,plain,
    ( ~ r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK1))
    | ~ r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK0))
    | ~ r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(k2_xboole_0(sK0,sK1))) ),
    inference(equality_resolution,[],[f168])).

fof(f168,plain,(
    ! [X2] :
      ( k1_setfam_1(k2_xboole_0(sK0,sK1)) != X2
      | ~ r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),X2),k1_setfam_1(sK1))
      | ~ r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),X2),k1_setfam_1(sK0))
      | ~ r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),X2),X2) ) ),
    inference(superposition,[],[f84,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK7(X0,X1,X2),X1)
      | ~ r2_hidden(sK7(X0,X1,X2),X0)
      | ~ r2_hidden(sK7(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f288,plain,
    ( spl10_8
    | spl10_10 ),
    inference(avatar_split_clause,[],[f257,f286,f280])).

fof(f257,plain,
    ( r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(sK0))
    | r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),k1_setfam_1(k2_xboole_0(sK0,sK1))),k1_setfam_1(k2_xboole_0(sK0,sK1))) ),
    inference(equality_resolution,[],[f166])).

fof(f166,plain,(
    ! [X0] :
      ( k1_setfam_1(k2_xboole_0(sK0,sK1)) != X0
      | r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),X0),k1_setfam_1(sK0))
      | r2_hidden(sK7(k1_setfam_1(sK0),k1_setfam_1(sK1),X0),X0) ) ),
    inference(superposition,[],[f84,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK7(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f76])).
%------------------------------------------------------------------------------
