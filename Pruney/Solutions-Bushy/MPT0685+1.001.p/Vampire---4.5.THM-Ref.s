%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0685+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 267 expanded)
%              Number of leaves         :   16 (  85 expanded)
%              Depth                    :   17
%              Number of atoms          :  483 (1439 expanded)
%              Number of equality atoms :   47 ( 196 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f404,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f92,f100,f300,f400])).

fof(f400,plain,
    ( spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f393,f88])).

fof(f88,plain,
    ( r2_hidden(sK5(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl10_3
  <=> r2_hidden(sK5(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f393,plain,
    ( ~ r2_hidden(sK5(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)
    | spl10_2
    | ~ spl10_4 ),
    inference(resolution,[],[f352,f83])).

fof(f83,plain,
    ( ~ r2_hidden(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))
    | spl10_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl10_2
  <=> r2_hidden(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f352,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK0,k10_relat_1(sK2,X0)))
        | ~ r2_hidden(sK5(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),X0) )
    | ~ spl10_4 ),
    inference(resolution,[],[f315,f310])).

fof(f310,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),X0)
        | r2_hidden(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK0,X0)) )
    | ~ spl10_4 ),
    inference(resolution,[],[f307,f52])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f307,plain,
    ( r2_hidden(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0)
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f302,f31])).

fof(f31,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f302,plain,
    ( r2_hidden(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl10_4 ),
    inference(resolution,[],[f99,f75])).

fof(f75,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | r2_hidden(X5,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f60,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f60,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK7(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X0)
                    & r2_hidden(sK7(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X0)
            & r2_hidden(sK7(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

fof(f99,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK5(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK0))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl10_4
  <=> r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK5(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f315,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,X1))
        | ~ r2_hidden(sK5(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),X1) )
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f312,f31])).

fof(f312,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),X1)
        | r2_hidden(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,X1))
        | ~ v1_relat_1(sK2) )
    | ~ spl10_4 ),
    inference(resolution,[],[f306,f55])).

fof(f55,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ r2_hidden(X7,X1)
      | r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK4(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK5(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X0) )
                | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK6(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK6(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f21,f24,f23,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK4(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK6(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK6(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f306,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK5(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK2)
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f301,f31])).

fof(f301,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK5(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl10_4 ),
    inference(resolution,[],[f99,f74])).

fof(f74,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X5,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f59,f45])).

fof(f59,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f300,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f298,f112])).

fof(f112,plain,
    ( r2_hidden(sK6(sK2,sK1,sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1)
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f109,f31])).

fof(f109,plain,
    ( r2_hidden(sK6(sK2,sK1,sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl10_2 ),
    inference(resolution,[],[f103,f56])).

fof(f56,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | r2_hidden(sK6(X0,X1,X6),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f103,plain,
    ( r2_hidden(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ spl10_2 ),
    inference(resolution,[],[f84,f53])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f84,plain,
    ( r2_hidden(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f298,plain,
    ( ~ r2_hidden(sK6(sK2,sK1,sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1)
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f292,f102])).

fof(f102,plain,
    ( r2_hidden(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0)
    | ~ spl10_2 ),
    inference(resolution,[],[f84,f54])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f292,plain,
    ( ~ r2_hidden(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0)
    | ~ r2_hidden(sK6(sK2,sK1,sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1)
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f177,f106])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),X0),k7_relat_1(sK2,sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f105,f79])).

fof(f79,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl10_1
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),X0),k7_relat_1(sK2,sK0))
        | ~ v1_relat_1(k7_relat_1(sK2,sK0)) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f101,f62])).

fof(f62,plain,(
    ~ sQ9_eqProxy(k10_relat_1(k7_relat_1(sK2,sK0),sK1),k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) ),
    inference(equality_proxy_replacement,[],[f32,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( sQ9_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ9_eqProxy])])).

fof(f32,plain,(
    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),X0),k7_relat_1(sK2,sK0))
        | sQ9_eqProxy(k10_relat_1(k7_relat_1(sK2,sK0),sK1),k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))
        | ~ v1_relat_1(k7_relat_1(sK2,sK0)) )
    | ~ spl10_2 ),
    inference(resolution,[],[f84,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X4),X0)
      | sQ9_eqProxy(k10_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f44,f61])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X4),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f177,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK6(sK2,sK1,sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))))),k7_relat_1(sK2,X0))
        | ~ r2_hidden(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),X0) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f174,f31])).

fof(f174,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK6(sK2,sK1,sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))))),k7_relat_1(sK2,X0))
        | ~ r2_hidden(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl10_2 ),
    inference(resolution,[],[f111,f73])).

fof(f73,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f58,f45])).

fof(f58,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f111,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK6(sK2,sK1,sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))))),sK2)
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f108,f31])).

fof(f108,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK6(sK2,sK1,sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))))),sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl10_2 ),
    inference(resolution,[],[f103,f57])).

fof(f57,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X6,sK6(X0,X1,X6)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK6(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f100,plain,
    ( spl10_2
    | spl10_4
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f95,f78,f97,f82])).

fof(f95,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK5(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK0))
    | r2_hidden(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f94,f79])).

fof(f94,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK5(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k7_relat_1(sK2,sK0))
    | r2_hidden(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f68,f62])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( sQ9_eqProxy(k10_relat_1(X0,X1),X2)
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f42,f61])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f92,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | spl10_1 ),
    inference(subsumption_resolution,[],[f90,f31])).

fof(f90,plain,
    ( ~ v1_relat_1(sK2)
    | spl10_1 ),
    inference(resolution,[],[f80,f45])).

fof(f80,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f89,plain,
    ( ~ spl10_1
    | spl10_2
    | spl10_3 ),
    inference(avatar_split_clause,[],[f76,f86,f82,f78])).

fof(f76,plain,
    ( r2_hidden(sK5(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)
    | r2_hidden(sK4(k7_relat_1(sK2,sK0),sK1,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f67,f62])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sQ9_eqProxy(k10_relat_1(X0,X1),X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f43,f61])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

%------------------------------------------------------------------------------
