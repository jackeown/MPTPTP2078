%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0523+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:35 EST 2020

% Result     : Theorem 4.72s
% Output     : Refutation 4.72s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 164 expanded)
%              Number of leaves         :   11 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  263 ( 643 expanded)
%              Number of equality atoms :   21 ( 102 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7105,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5447,f5458,f5501,f7052,f7101])).

fof(f7101,plain,
    ( ~ spl152_7
    | spl152_8
    | ~ spl152_9 ),
    inference(avatar_contradiction_clause,[],[f7091])).

fof(f7091,plain,
    ( $false
    | ~ spl152_7
    | spl152_8
    | ~ spl152_9 ),
    inference(unit_resulting_resolution,[],[f1782,f5446,f5441,f7076,f2744])).

fof(f2744,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X3)
      | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | ~ r2_hidden(X1,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f1701])).

fof(f1701,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f1700])).

fof(f1700,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f1305])).

fof(f1305,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f749])).

fof(f749,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_relat_1)).

fof(f7076,plain,
    ( r2_hidden(k4_tarski(sK48(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3))),sK49(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3)))),sK4)
    | ~ spl152_7
    | spl152_8 ),
    inference(subsumption_resolution,[],[f7056,f5441])).

fof(f7056,plain,
    ( r2_hidden(k4_tarski(sK48(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3))),sK49(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3)))),sK4)
    | r2_hidden(k4_tarski(sK48(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3))),sK49(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3)))),k5_relat_1(sK4,k6_relat_1(sK3)))
    | ~ spl152_7 ),
    inference(subsumption_resolution,[],[f4147,f5437])).

fof(f5437,plain,
    ( v1_relat_1(k5_relat_1(sK4,k6_relat_1(sK3)))
    | ~ spl152_7 ),
    inference(avatar_component_clause,[],[f5436])).

fof(f5436,plain,
    ( spl152_7
  <=> v1_relat_1(k5_relat_1(sK4,k6_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl152_7])])).

fof(f4147,plain,
    ( r2_hidden(k4_tarski(sK48(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3))),sK49(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3)))),sK4)
    | r2_hidden(k4_tarski(sK48(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3))),sK49(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3)))),k5_relat_1(sK4,k6_relat_1(sK3)))
    | ~ v1_relat_1(k5_relat_1(sK4,k6_relat_1(sK3))) ),
    inference(subsumption_resolution,[],[f4146,f1782])).

fof(f4146,plain,
    ( r2_hidden(k4_tarski(sK48(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3))),sK49(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3)))),sK4)
    | r2_hidden(k4_tarski(sK48(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3))),sK49(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3)))),k5_relat_1(sK4,k6_relat_1(sK3)))
    | ~ v1_relat_1(k5_relat_1(sK4,k6_relat_1(sK3)))
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f3369,f3216])).

fof(f3216,plain,(
    ~ sQ151_eqProxy(k8_relat_1(sK3,sK4),k5_relat_1(sK4,k6_relat_1(sK3))) ),
    inference(equality_proxy_replacement,[],[f1783,f3198])).

fof(f3198,plain,(
    ! [X1,X0] :
      ( sQ151_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ151_eqProxy])])).

fof(f1783,plain,(
    k8_relat_1(sK3,sK4) != k5_relat_1(sK4,k6_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f1365])).

fof(f1365,plain,
    ( k8_relat_1(sK3,sK4) != k5_relat_1(sK4,k6_relat_1(sK3))
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f787,f1364])).

fof(f1364,plain,
    ( ? [X0,X1] :
        ( k8_relat_1(X0,X1) != k5_relat_1(X1,k6_relat_1(X0))
        & v1_relat_1(X1) )
   => ( k8_relat_1(sK3,sK4) != k5_relat_1(sK4,k6_relat_1(sK3))
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f787,plain,(
    ? [X0,X1] :
      ( k8_relat_1(X0,X1) != k5_relat_1(X1,k6_relat_1(X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f700])).

fof(f700,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(negated_conjecture,[],[f699])).

fof(f699,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f3369,plain,(
    ! [X2,X0,X1] :
      ( sQ151_eqProxy(k8_relat_1(X0,X1),X2)
      | r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f2115,f3198])).

fof(f2115,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1461])).

fof(f1461,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK49(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X1)
                    & r2_hidden(sK49(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK48,sK49])],[f1459,f1460])).

fof(f1460,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X1)
          | ~ r2_hidden(sK49(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X1)
            & r2_hidden(sK49(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1459,plain,(
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
    inference(rectify,[],[f1458])).

fof(f1458,plain,(
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
    inference(flattening,[],[f1457])).

fof(f1457,plain,(
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
    inference(nnf_transformation,[],[f939])).

fof(f939,plain,(
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

fof(f5441,plain,
    ( ~ r2_hidden(k4_tarski(sK48(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3))),sK49(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3)))),k5_relat_1(sK4,k6_relat_1(sK3)))
    | spl152_8 ),
    inference(avatar_component_clause,[],[f5440])).

fof(f5440,plain,
    ( spl152_8
  <=> r2_hidden(k4_tarski(sK48(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3))),sK49(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3)))),k5_relat_1(sK4,k6_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl152_8])])).

fof(f5446,plain,
    ( r2_hidden(sK49(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3))),sK3)
    | ~ spl152_9 ),
    inference(avatar_component_clause,[],[f5444])).

fof(f5444,plain,
    ( spl152_9
  <=> r2_hidden(sK49(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl152_9])])).

fof(f1782,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f1365])).

fof(f7052,plain,
    ( ~ spl152_7
    | ~ spl152_8
    | ~ spl152_9 ),
    inference(avatar_contradiction_clause,[],[f7042])).

fof(f7042,plain,
    ( $false
    | ~ spl152_7
    | ~ spl152_8
    | ~ spl152_9 ),
    inference(unit_resulting_resolution,[],[f1782,f5437,f3216,f5446,f5442,f5498,f3368])).

fof(f3368,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK49(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X1)
      | sQ151_eqProxy(k8_relat_1(X0,X1),X2)
      | ~ r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f2116,f3198])).

fof(f2116,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X1)
      | ~ r2_hidden(sK49(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1461])).

fof(f5498,plain,
    ( r2_hidden(k4_tarski(sK48(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3))),sK49(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3)))),sK4)
    | ~ spl152_8 ),
    inference(subsumption_resolution,[],[f5484,f1782])).

fof(f5484,plain,
    ( r2_hidden(k4_tarski(sK48(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3))),sK49(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3)))),sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl152_8 ),
    inference(resolution,[],[f5442,f2743])).

fof(f2743,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | r2_hidden(k4_tarski(X0,X1),X3)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f1701])).

fof(f5442,plain,
    ( r2_hidden(k4_tarski(sK48(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3))),sK49(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3)))),k5_relat_1(sK4,k6_relat_1(sK3)))
    | ~ spl152_8 ),
    inference(avatar_component_clause,[],[f5440])).

fof(f5501,plain,
    ( ~ spl152_8
    | spl152_9 ),
    inference(avatar_contradiction_clause,[],[f5500])).

fof(f5500,plain,
    ( $false
    | ~ spl152_8
    | spl152_9 ),
    inference(subsumption_resolution,[],[f5499,f1782])).

fof(f5499,plain,
    ( ~ v1_relat_1(sK4)
    | ~ spl152_8
    | spl152_9 ),
    inference(subsumption_resolution,[],[f5485,f5445])).

fof(f5445,plain,
    ( ~ r2_hidden(sK49(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3))),sK3)
    | spl152_9 ),
    inference(avatar_component_clause,[],[f5444])).

fof(f5485,plain,
    ( r2_hidden(sK49(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3))),sK3)
    | ~ v1_relat_1(sK4)
    | ~ spl152_8 ),
    inference(resolution,[],[f5442,f2742])).

fof(f2742,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | r2_hidden(X1,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f1701])).

fof(f5458,plain,(
    spl152_7 ),
    inference(avatar_contradiction_clause,[],[f5457])).

fof(f5457,plain,
    ( $false
    | spl152_7 ),
    inference(subsumption_resolution,[],[f5456,f1782])).

fof(f5456,plain,
    ( ~ v1_relat_1(sK4)
    | spl152_7 ),
    inference(subsumption_resolution,[],[f5451,f1799])).

fof(f1799,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f656])).

fof(f656,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f5451,plain,
    ( ~ v1_relat_1(k6_relat_1(sK3))
    | ~ v1_relat_1(sK4)
    | spl152_7 ),
    inference(resolution,[],[f5438,f2281])).

fof(f2281,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1102])).

fof(f1102,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1101])).

fof(f1101,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f655])).

fof(f655,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f5438,plain,
    ( ~ v1_relat_1(k5_relat_1(sK4,k6_relat_1(sK3)))
    | spl152_7 ),
    inference(avatar_component_clause,[],[f5436])).

fof(f5447,plain,
    ( ~ spl152_7
    | spl152_8
    | spl152_9 ),
    inference(avatar_split_clause,[],[f4143,f5444,f5440,f5436])).

fof(f4143,plain,
    ( r2_hidden(sK49(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3))),sK3)
    | r2_hidden(k4_tarski(sK48(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3))),sK49(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3)))),k5_relat_1(sK4,k6_relat_1(sK3)))
    | ~ v1_relat_1(k5_relat_1(sK4,k6_relat_1(sK3))) ),
    inference(subsumption_resolution,[],[f4142,f1782])).

fof(f4142,plain,
    ( r2_hidden(sK49(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3))),sK3)
    | r2_hidden(k4_tarski(sK48(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3))),sK49(sK3,sK4,k5_relat_1(sK4,k6_relat_1(sK3)))),k5_relat_1(sK4,k6_relat_1(sK3)))
    | ~ v1_relat_1(k5_relat_1(sK4,k6_relat_1(sK3)))
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f3370,f3216])).

fof(f3370,plain,(
    ! [X2,X0,X1] :
      ( sQ151_eqProxy(k8_relat_1(X0,X1),X2)
      | r2_hidden(sK49(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f2114,f3198])).

fof(f2114,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(sK49(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK48(X0,X1,X2),sK49(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1461])).
%------------------------------------------------------------------------------
