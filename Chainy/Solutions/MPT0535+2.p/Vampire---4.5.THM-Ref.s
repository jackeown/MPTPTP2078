%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0535+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:35 EST 2020

% Result     : Theorem 18.46s
% Output     : Refutation 18.46s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 373 expanded)
%              Number of leaves         :   16 ( 109 expanded)
%              Depth                    :   16
%              Number of atoms          :  481 (1982 expanded)
%              Number of equality atoms :   36 ( 265 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14134,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5415,f5436,f8340,f8369,f8391,f8393,f8452,f14055,f14065,f14085,f14127,f14133])).

fof(f14133,plain,
    ( ~ spl153_8
    | spl153_24 ),
    inference(avatar_contradiction_clause,[],[f14130])).

fof(f14130,plain,
    ( $false
    | ~ spl153_8
    | spl153_24 ),
    inference(unit_resulting_resolution,[],[f5410,f14050,f3122])).

fof(f3122,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f2668])).

fof(f2668,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1701])).

fof(f1701,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK125(X0,X1,X2),X1)
            | ~ r2_hidden(sK125(X0,X1,X2),X0)
            | ~ r2_hidden(sK125(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK125(X0,X1,X2),X1)
              & r2_hidden(sK125(X0,X1,X2),X0) )
            | r2_hidden(sK125(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK125])],[f1699,f1700])).

fof(f1700,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK125(X0,X1,X2),X1)
          | ~ r2_hidden(sK125(X0,X1,X2),X0)
          | ~ r2_hidden(sK125(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK125(X0,X1,X2),X1)
            & r2_hidden(sK125(X0,X1,X2),X0) )
          | r2_hidden(sK125(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1699,plain,(
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
    inference(rectify,[],[f1698])).

fof(f1698,plain,(
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
    inference(flattening,[],[f1697])).

fof(f1697,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f14050,plain,
    ( ~ r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k8_relat_1(sK3,sK5))
    | spl153_24 ),
    inference(avatar_component_clause,[],[f14048])).

fof(f14048,plain,
    ( spl153_24
  <=> r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k8_relat_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_24])])).

fof(f5410,plain,
    ( r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ spl153_8 ),
    inference(avatar_component_clause,[],[f5408])).

fof(f5408,plain,
    ( spl153_8
  <=> r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_8])])).

fof(f14127,plain,
    ( ~ spl153_7
    | ~ spl153_8
    | ~ spl153_9
    | ~ spl153_24 ),
    inference(avatar_contradiction_clause,[],[f14126])).

fof(f14126,plain,
    ( $false
    | ~ spl153_7
    | ~ spl153_8
    | ~ spl153_9
    | ~ spl153_24 ),
    inference(unit_resulting_resolution,[],[f1812,f14049,f14121,f4153])).

fof(f4153,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X5,X6),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f3057,f2101])).

fof(f2101,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f910])).

fof(f910,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f658])).

fof(f658,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f3057,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f2148])).

fof(f2148,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1491])).

fof(f1491,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK49,sK50])],[f1489,f1490])).

fof(f1490,plain,(
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

fof(f1489,plain,(
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
    inference(rectify,[],[f1488])).

fof(f1488,plain,(
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
    inference(flattening,[],[f1487])).

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
    inference(nnf_transformation,[],[f959])).

fof(f959,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

fof(f14121,plain,
    ( ~ r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | ~ spl153_7
    | ~ spl153_8
    | ~ spl153_9 ),
    inference(subsumption_resolution,[],[f14087,f5410])).

fof(f14087,plain,
    ( ~ r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | ~ r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ spl153_7
    | ~ spl153_9 ),
    inference(subsumption_resolution,[],[f8371,f5414])).

fof(f5414,plain,
    ( r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),k3_xboole_0(sK3,sK4))
    | ~ spl153_9 ),
    inference(avatar_component_clause,[],[f5412])).

fof(f5412,plain,
    ( spl153_9
  <=> r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),k3_xboole_0(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_9])])).

fof(f8371,plain,
    ( ~ r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | ~ r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),k3_xboole_0(sK3,sK4))
    | ~ r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ spl153_7 ),
    inference(subsumption_resolution,[],[f4165,f5405])).

fof(f5405,plain,
    ( v1_relat_1(k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ spl153_7 ),
    inference(avatar_component_clause,[],[f5404])).

fof(f5404,plain,
    ( spl153_7
  <=> v1_relat_1(k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_7])])).

fof(f4165,plain,
    ( ~ r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | ~ r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),k3_xboole_0(sK3,sK4))
    | ~ r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ v1_relat_1(k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))) ),
    inference(subsumption_resolution,[],[f4164,f1812])).

fof(f4164,plain,
    ( ~ r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | ~ r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),k3_xboole_0(sK3,sK4))
    | ~ r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ v1_relat_1(k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f3415,f3258])).

fof(f3258,plain,(
    ~ sQ152_eqProxy(k8_relat_1(k3_xboole_0(sK3,sK4),sK5),k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))) ),
    inference(equality_proxy_replacement,[],[f1813,f3240])).

fof(f3240,plain,(
    ! [X1,X0] :
      ( sQ152_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ152_eqProxy])])).

fof(f1813,plain,(
    k8_relat_1(k3_xboole_0(sK3,sK4),sK5) != k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f1395])).

fof(f1395,plain,
    ( k8_relat_1(k3_xboole_0(sK3,sK4),sK5) != k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f799,f1394])).

fof(f1394,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(k3_xboole_0(X0,X1),X2) != k3_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
        & v1_relat_1(X2) )
   => ( k8_relat_1(k3_xboole_0(sK3,sK4),sK5) != k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f799,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(k3_xboole_0(X0,X1),X2) != k3_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f712])).

fof(f712,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k8_relat_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f711])).

fof(f711,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_relat_1)).

fof(f3415,plain,(
    ! [X2,X0,X1] :
      ( sQ152_eqProxy(k8_relat_1(X0,X1),X2)
      | ~ r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X1)
      | ~ r2_hidden(sK50(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f2152,f3240])).

fof(f2152,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X1)
      | ~ r2_hidden(sK50(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1491])).

fof(f14049,plain,
    ( r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k8_relat_1(sK3,sK5))
    | ~ spl153_24 ),
    inference(avatar_component_clause,[],[f14048])).

fof(f1812,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f1395])).

fof(f14085,plain,
    ( ~ spl153_7
    | spl153_8
    | ~ spl153_21
    | spl153_25 ),
    inference(avatar_contradiction_clause,[],[f14084])).

fof(f14084,plain,
    ( $false
    | ~ spl153_7
    | spl153_8
    | ~ spl153_21
    | spl153_25 ),
    inference(subsumption_resolution,[],[f14083,f1812])).

fof(f14083,plain,
    ( ~ v1_relat_1(sK5)
    | ~ spl153_7
    | spl153_8
    | ~ spl153_21
    | spl153_25 ),
    inference(subsumption_resolution,[],[f14082,f8338])).

fof(f8338,plain,
    ( r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK4)
    | ~ spl153_21 ),
    inference(avatar_component_clause,[],[f8337])).

fof(f8337,plain,
    ( spl153_21
  <=> r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_21])])).

fof(f14082,plain,
    ( ~ r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK4)
    | ~ v1_relat_1(sK5)
    | ~ spl153_7
    | spl153_8
    | spl153_25 ),
    inference(subsumption_resolution,[],[f14079,f8481])).

fof(f8481,plain,
    ( r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | ~ spl153_7
    | spl153_8 ),
    inference(subsumption_resolution,[],[f8370,f5409])).

fof(f5409,plain,
    ( ~ r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | spl153_8 ),
    inference(avatar_component_clause,[],[f5408])).

fof(f8370,plain,
    ( r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ spl153_7 ),
    inference(subsumption_resolution,[],[f4163,f5405])).

fof(f4163,plain,
    ( r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ v1_relat_1(k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))) ),
    inference(subsumption_resolution,[],[f4162,f1812])).

fof(f4162,plain,
    ( r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ v1_relat_1(k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f3416,f3258])).

fof(f3416,plain,(
    ! [X2,X0,X1] :
      ( sQ152_eqProxy(k8_relat_1(X0,X1),X2)
      | r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f2151,f3240])).

fof(f2151,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1491])).

fof(f14079,plain,
    ( ~ r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | ~ r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK4)
    | ~ v1_relat_1(sK5)
    | spl153_25 ),
    inference(resolution,[],[f14054,f4154])).

fof(f4154,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f3056,f2101])).

fof(f3056,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f2149])).

fof(f2149,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1491])).

fof(f14054,plain,
    ( ~ r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k8_relat_1(sK4,sK5))
    | spl153_25 ),
    inference(avatar_component_clause,[],[f14052])).

fof(f14052,plain,
    ( spl153_25
  <=> r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k8_relat_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_25])])).

fof(f14065,plain,
    ( ~ spl153_7
    | spl153_8
    | ~ spl153_20
    | spl153_24 ),
    inference(avatar_contradiction_clause,[],[f14064])).

fof(f14064,plain,
    ( $false
    | ~ spl153_7
    | spl153_8
    | ~ spl153_20
    | spl153_24 ),
    inference(subsumption_resolution,[],[f14063,f1812])).

fof(f14063,plain,
    ( ~ v1_relat_1(sK5)
    | ~ spl153_7
    | spl153_8
    | ~ spl153_20
    | spl153_24 ),
    inference(subsumption_resolution,[],[f14062,f8334])).

fof(f8334,plain,
    ( r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK3)
    | ~ spl153_20 ),
    inference(avatar_component_clause,[],[f8333])).

fof(f8333,plain,
    ( spl153_20
  <=> r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_20])])).

fof(f14062,plain,
    ( ~ r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK3)
    | ~ v1_relat_1(sK5)
    | ~ spl153_7
    | spl153_8
    | spl153_24 ),
    inference(subsumption_resolution,[],[f14059,f8481])).

fof(f14059,plain,
    ( ~ r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),sK5)
    | ~ r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK3)
    | ~ v1_relat_1(sK5)
    | spl153_24 ),
    inference(resolution,[],[f14050,f4154])).

fof(f14055,plain,
    ( ~ spl153_24
    | ~ spl153_25
    | spl153_8 ),
    inference(avatar_split_clause,[],[f8471,f5408,f14052,f14048])).

fof(f8471,plain,
    ( ~ r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k8_relat_1(sK4,sK5))
    | ~ r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k8_relat_1(sK3,sK5))
    | spl153_8 ),
    inference(resolution,[],[f5409,f3120])).

fof(f3120,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f2670])).

fof(f2670,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1701])).

fof(f8452,plain,
    ( ~ spl153_8
    | spl153_21 ),
    inference(avatar_contradiction_clause,[],[f8451])).

fof(f8451,plain,
    ( $false
    | ~ spl153_8
    | spl153_21 ),
    inference(subsumption_resolution,[],[f8450,f1812])).

fof(f8450,plain,
    ( ~ v1_relat_1(sK5)
    | ~ spl153_8
    | spl153_21 ),
    inference(subsumption_resolution,[],[f8444,f8339])).

fof(f8339,plain,
    ( ~ r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK4)
    | spl153_21 ),
    inference(avatar_component_clause,[],[f8337])).

fof(f8444,plain,
    ( r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK4)
    | ~ v1_relat_1(sK5)
    | ~ spl153_8 ),
    inference(resolution,[],[f8404,f4150])).

fof(f4150,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | r2_hidden(X6,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f3058,f2101])).

fof(f3058,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f2147])).

fof(f2147,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1491])).

fof(f8404,plain,
    ( r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k8_relat_1(sK4,sK5))
    | ~ spl153_8 ),
    inference(resolution,[],[f5410,f3121])).

fof(f3121,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f2669])).

fof(f2669,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1701])).

fof(f8393,plain,
    ( ~ spl153_9
    | spl153_21 ),
    inference(avatar_contradiction_clause,[],[f8392])).

fof(f8392,plain,
    ( $false
    | ~ spl153_9
    | spl153_21 ),
    inference(subsumption_resolution,[],[f8383,f8339])).

fof(f8383,plain,
    ( r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK4)
    | ~ spl153_9 ),
    inference(resolution,[],[f5414,f3121])).

fof(f8391,plain,
    ( ~ spl153_9
    | spl153_20 ),
    inference(avatar_contradiction_clause,[],[f8390])).

fof(f8390,plain,
    ( $false
    | ~ spl153_9
    | spl153_20 ),
    inference(subsumption_resolution,[],[f8382,f8335])).

fof(f8335,plain,
    ( ~ r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK3)
    | spl153_20 ),
    inference(avatar_component_clause,[],[f8333])).

fof(f8382,plain,
    ( r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK3)
    | ~ spl153_9 ),
    inference(resolution,[],[f5414,f3122])).

fof(f8369,plain,
    ( ~ spl153_8
    | spl153_20 ),
    inference(avatar_contradiction_clause,[],[f8368])).

fof(f8368,plain,
    ( $false
    | ~ spl153_8
    | spl153_20 ),
    inference(subsumption_resolution,[],[f8367,f1812])).

fof(f8367,plain,
    ( ~ v1_relat_1(sK5)
    | ~ spl153_8
    | spl153_20 ),
    inference(subsumption_resolution,[],[f8361,f8335])).

fof(f8361,plain,
    ( r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK3)
    | ~ v1_relat_1(sK5)
    | ~ spl153_8 ),
    inference(resolution,[],[f5439,f4150])).

fof(f5439,plain,
    ( r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k8_relat_1(sK3,sK5))
    | ~ spl153_8 ),
    inference(resolution,[],[f5410,f3122])).

fof(f8340,plain,
    ( ~ spl153_20
    | ~ spl153_21
    | spl153_9 ),
    inference(avatar_split_clause,[],[f5428,f5412,f8337,f8333])).

fof(f5428,plain,
    ( ~ r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK4)
    | ~ r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK3)
    | spl153_9 ),
    inference(resolution,[],[f5413,f3120])).

fof(f5413,plain,
    ( ~ r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),k3_xboole_0(sK3,sK4))
    | spl153_9 ),
    inference(avatar_component_clause,[],[f5412])).

fof(f5436,plain,(
    spl153_7 ),
    inference(avatar_contradiction_clause,[],[f5435])).

fof(f5435,plain,
    ( $false
    | spl153_7 ),
    inference(subsumption_resolution,[],[f5430,f1812])).

fof(f5430,plain,
    ( ~ v1_relat_1(sK5)
    | spl153_7 ),
    inference(resolution,[],[f5418,f2101])).

fof(f5418,plain,
    ( ~ v1_relat_1(k8_relat_1(sK3,sK5))
    | spl153_7 ),
    inference(resolution,[],[f5406,f2104])).

fof(f2104,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f913])).

fof(f913,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f668])).

fof(f668,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f5406,plain,
    ( ~ v1_relat_1(k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | spl153_7 ),
    inference(avatar_component_clause,[],[f5404])).

fof(f5415,plain,
    ( ~ spl153_7
    | spl153_8
    | spl153_9 ),
    inference(avatar_split_clause,[],[f4161,f5412,f5408,f5404])).

fof(f4161,plain,
    ( r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),k3_xboole_0(sK3,sK4))
    | r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ v1_relat_1(k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))) ),
    inference(subsumption_resolution,[],[f4160,f1812])).

fof(f4160,plain,
    ( r2_hidden(sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),k3_xboole_0(sK3,sK4))
    | r2_hidden(k4_tarski(sK49(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5))),sK50(k3_xboole_0(sK3,sK4),sK5,k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))),k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ v1_relat_1(k3_xboole_0(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK5)))
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f3417,f3258])).

fof(f3417,plain,(
    ! [X2,X0,X1] :
      ( sQ152_eqProxy(k8_relat_1(X0,X1),X2)
      | r2_hidden(sK50(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f2150,f3240])).

fof(f2150,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(sK50(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1491])).
%------------------------------------------------------------------------------
