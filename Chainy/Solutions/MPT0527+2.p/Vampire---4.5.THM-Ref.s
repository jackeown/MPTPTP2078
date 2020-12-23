%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0527+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:35 EST 2020

% Result     : Theorem 12.83s
% Output     : Refutation 12.96s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 335 expanded)
%              Number of leaves         :   12 (  94 expanded)
%              Depth                    :   19
%              Number of atoms          :  434 (1820 expanded)
%              Number of equality atoms :   36 ( 241 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10988,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4267,f5499,f5507,f5527,f7634,f10987])).

fof(f10987,plain,
    ( ~ spl153_3
    | ~ spl153_9
    | spl153_10
    | ~ spl153_11 ),
    inference(avatar_contradiction_clause,[],[f10986])).

fof(f10986,plain,
    ( $false
    | ~ spl153_3
    | ~ spl153_9
    | spl153_10
    | ~ spl153_11 ),
    inference(subsumption_resolution,[],[f10985,f5498])).

fof(f5498,plain,
    ( r2_hidden(sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK3)
    | ~ spl153_11 ),
    inference(avatar_component_clause,[],[f5496])).

fof(f5496,plain,
    ( spl153_11
  <=> r2_hidden(sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_11])])).

fof(f10985,plain,
    ( ~ r2_hidden(sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK3)
    | ~ spl153_3
    | ~ spl153_9
    | spl153_10 ),
    inference(subsumption_resolution,[],[f10982,f7658])).

fof(f7658,plain,
    ( r2_hidden(sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK4)
    | ~ spl153_3
    | ~ spl153_9
    | spl153_10 ),
    inference(subsumption_resolution,[],[f7652,f1791])).

fof(f1791,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f1374])).

fof(f1374,plain,
    ( k8_relat_1(sK3,k8_relat_1(sK4,sK5)) != k8_relat_1(k3_xboole_0(sK3,sK4),sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f791,f1373])).

fof(f1373,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(k3_xboole_0(X0,X1),X2)
        & v1_relat_1(X2) )
   => ( k8_relat_1(sK3,k8_relat_1(sK4,sK5)) != k8_relat_1(k3_xboole_0(sK3,sK4),sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f791,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(k3_xboole_0(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f704])).

fof(f704,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f703])).

fof(f703,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

fof(f7652,plain,
    ( r2_hidden(sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK4)
    | ~ v1_relat_1(sK5)
    | ~ spl153_3
    | ~ spl153_9
    | spl153_10 ),
    inference(resolution,[],[f7650,f4116])).

fof(f4116,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | r2_hidden(X6,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f3029,f2080])).

fof(f2080,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f902])).

fof(f902,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f658])).

fof(f658,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f3029,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f2124])).

fof(f2124,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1470])).

fof(f1470,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK49,sK50])],[f1468,f1469])).

fof(f1469,plain,(
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

fof(f1468,plain,(
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
    inference(rectify,[],[f1467])).

fof(f1467,plain,(
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
    inference(flattening,[],[f1466])).

fof(f1466,plain,(
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
    inference(nnf_transformation,[],[f948])).

fof(f948,plain,(
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

fof(f7650,plain,
    ( r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),k8_relat_1(sK4,sK5))
    | ~ spl153_3
    | ~ spl153_9
    | spl153_10 ),
    inference(subsumption_resolution,[],[f7639,f5493])).

fof(f5493,plain,
    ( ~ r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))
    | spl153_10 ),
    inference(avatar_component_clause,[],[f5492])).

fof(f5492,plain,
    ( spl153_10
  <=> r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_10])])).

fof(f7639,plain,
    ( r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),k8_relat_1(sK4,sK5))
    | r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))
    | ~ spl153_3
    | ~ spl153_9 ),
    inference(subsumption_resolution,[],[f7638,f4249])).

fof(f4249,plain,
    ( v1_relat_1(k8_relat_1(sK4,sK5))
    | ~ spl153_3 ),
    inference(avatar_component_clause,[],[f4248])).

fof(f4248,plain,
    ( spl153_3
  <=> v1_relat_1(k8_relat_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_3])])).

fof(f7638,plain,
    ( r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),k8_relat_1(sK4,sK5))
    | r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))
    | ~ v1_relat_1(k8_relat_1(sK4,sK5))
    | ~ spl153_9 ),
    inference(subsumption_resolution,[],[f4127,f5489])).

fof(f5489,plain,
    ( v1_relat_1(k8_relat_1(k3_xboole_0(sK3,sK4),sK5))
    | ~ spl153_9 ),
    inference(avatar_component_clause,[],[f5488])).

fof(f5488,plain,
    ( spl153_9
  <=> v1_relat_1(k8_relat_1(k3_xboole_0(sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl153_9])])).

fof(f4127,plain,
    ( r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),k8_relat_1(sK4,sK5))
    | r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK3,sK4),sK5))
    | ~ v1_relat_1(k8_relat_1(sK4,sK5)) ),
    inference(resolution,[],[f3386,f3229])).

fof(f3229,plain,(
    ~ sQ152_eqProxy(k8_relat_1(sK3,k8_relat_1(sK4,sK5)),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)) ),
    inference(equality_proxy_replacement,[],[f1792,f3211])).

fof(f3211,plain,(
    ! [X1,X0] :
      ( sQ152_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ152_eqProxy])])).

fof(f1792,plain,(
    k8_relat_1(sK3,k8_relat_1(sK4,sK5)) != k8_relat_1(k3_xboole_0(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f1374])).

fof(f3386,plain,(
    ! [X2,X0,X1] :
      ( sQ152_eqProxy(k8_relat_1(X0,X1),X2)
      | r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f2128,f3211])).

fof(f2128,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1470])).

fof(f10982,plain,
    ( ~ r2_hidden(sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK4)
    | ~ r2_hidden(sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK3)
    | ~ spl153_3
    | ~ spl153_9
    | spl153_10 ),
    inference(resolution,[],[f10979,f3091])).

fof(f3091,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f2641])).

fof(f2641,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1680])).

fof(f1680,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK125])],[f1678,f1679])).

fof(f1679,plain,(
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

fof(f1678,plain,(
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
    inference(rectify,[],[f1677])).

fof(f1677,plain,(
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
    inference(flattening,[],[f1676])).

fof(f1676,plain,(
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

fof(f10979,plain,
    ( ~ r2_hidden(sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),k3_xboole_0(sK3,sK4))
    | ~ spl153_3
    | ~ spl153_9
    | spl153_10 ),
    inference(subsumption_resolution,[],[f7642,f7657])).

fof(f7657,plain,
    ( r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),sK5)
    | ~ spl153_3
    | ~ spl153_9
    | spl153_10 ),
    inference(subsumption_resolution,[],[f7651,f1791])).

fof(f7651,plain,
    ( r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl153_3
    | ~ spl153_9
    | spl153_10 ),
    inference(resolution,[],[f7650,f4117])).

fof(f4117,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X5,X6),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f3028,f2080])).

fof(f3028,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f2125])).

fof(f2125,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1470])).

fof(f7642,plain,
    ( ~ r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),sK5)
    | ~ r2_hidden(sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),k3_xboole_0(sK3,sK4))
    | spl153_10 ),
    inference(subsumption_resolution,[],[f7641,f1791])).

fof(f7641,plain,
    ( ~ r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),sK5)
    | ~ r2_hidden(sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),k3_xboole_0(sK3,sK4))
    | ~ v1_relat_1(sK5)
    | spl153_10 ),
    inference(resolution,[],[f5493,f4118])).

fof(f4118,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f3027,f2080])).

fof(f3027,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f2126])).

fof(f2126,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1470])).

fof(f7634,plain,
    ( ~ spl153_3
    | ~ spl153_9
    | ~ spl153_10
    | ~ spl153_11 ),
    inference(avatar_contradiction_clause,[],[f7629])).

fof(f7629,plain,
    ( $false
    | ~ spl153_3
    | ~ spl153_9
    | ~ spl153_10
    | ~ spl153_11 ),
    inference(unit_resulting_resolution,[],[f1791,f5520,f5735,f5515,f4118])).

fof(f5515,plain,
    ( r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),sK5)
    | ~ spl153_10 ),
    inference(subsumption_resolution,[],[f5509,f1791])).

fof(f5509,plain,
    ( r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl153_10 ),
    inference(resolution,[],[f5494,f4117])).

fof(f5494,plain,
    ( r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))
    | ~ spl153_10 ),
    inference(avatar_component_clause,[],[f5492])).

fof(f5735,plain,
    ( ~ r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),k8_relat_1(sK4,sK5))
    | ~ spl153_3
    | ~ spl153_9
    | ~ spl153_10
    | ~ spl153_11 ),
    inference(subsumption_resolution,[],[f5734,f4249])).

fof(f5734,plain,
    ( ~ r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),k8_relat_1(sK4,sK5))
    | ~ v1_relat_1(k8_relat_1(sK4,sK5))
    | ~ spl153_9
    | ~ spl153_10
    | ~ spl153_11 ),
    inference(subsumption_resolution,[],[f5733,f5489])).

fof(f5733,plain,
    ( ~ r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),k8_relat_1(sK4,sK5))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK3,sK4),sK5))
    | ~ v1_relat_1(k8_relat_1(sK4,sK5))
    | ~ spl153_10
    | ~ spl153_11 ),
    inference(subsumption_resolution,[],[f5732,f5494])).

fof(f5732,plain,
    ( ~ r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),k8_relat_1(sK4,sK5))
    | ~ r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK3,sK4),sK5))
    | ~ v1_relat_1(k8_relat_1(sK4,sK5))
    | ~ spl153_11 ),
    inference(subsumption_resolution,[],[f4128,f5498])).

fof(f4128,plain,
    ( ~ r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),k8_relat_1(sK4,sK5))
    | ~ r2_hidden(sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK3)
    | ~ r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK3,sK4),sK5))
    | ~ v1_relat_1(k8_relat_1(sK4,sK5)) ),
    inference(resolution,[],[f3385,f3229])).

fof(f3385,plain,(
    ! [X2,X0,X1] :
      ( sQ152_eqProxy(k8_relat_1(X0,X1),X2)
      | ~ r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X1)
      | ~ r2_hidden(sK50(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f2129,f3211])).

fof(f2129,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X1)
      | ~ r2_hidden(sK50(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1470])).

fof(f5520,plain,
    ( r2_hidden(sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK4)
    | ~ spl153_10 ),
    inference(resolution,[],[f5516,f3092])).

fof(f3092,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f2640])).

fof(f2640,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1680])).

fof(f5516,plain,
    ( r2_hidden(sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),k3_xboole_0(sK3,sK4))
    | ~ spl153_10 ),
    inference(subsumption_resolution,[],[f5510,f1791])).

fof(f5510,plain,
    ( r2_hidden(sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),k3_xboole_0(sK3,sK4))
    | ~ v1_relat_1(sK5)
    | ~ spl153_10 ),
    inference(resolution,[],[f5494,f4116])).

fof(f5527,plain,
    ( ~ spl153_10
    | spl153_11 ),
    inference(avatar_contradiction_clause,[],[f5526])).

fof(f5526,plain,
    ( $false
    | ~ spl153_10
    | spl153_11 ),
    inference(subsumption_resolution,[],[f5519,f5497])).

fof(f5497,plain,
    ( ~ r2_hidden(sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK3)
    | spl153_11 ),
    inference(avatar_component_clause,[],[f5496])).

fof(f5519,plain,
    ( r2_hidden(sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK3)
    | ~ spl153_10 ),
    inference(resolution,[],[f5516,f3093])).

fof(f3093,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f2639])).

fof(f2639,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1680])).

fof(f5507,plain,(
    spl153_9 ),
    inference(avatar_contradiction_clause,[],[f5506])).

fof(f5506,plain,
    ( $false
    | spl153_9 ),
    inference(subsumption_resolution,[],[f5501,f1791])).

fof(f5501,plain,
    ( ~ v1_relat_1(sK5)
    | spl153_9 ),
    inference(resolution,[],[f5490,f2080])).

fof(f5490,plain,
    ( ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK3,sK4),sK5))
    | spl153_9 ),
    inference(avatar_component_clause,[],[f5488])).

fof(f5499,plain,
    ( ~ spl153_9
    | spl153_10
    | spl153_11
    | ~ spl153_3 ),
    inference(avatar_split_clause,[],[f5480,f4248,f5496,f5492,f5488])).

fof(f5480,plain,
    ( r2_hidden(sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK3)
    | r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK3,sK4),sK5))
    | ~ spl153_3 ),
    inference(subsumption_resolution,[],[f4126,f4249])).

fof(f4126,plain,
    ( r2_hidden(sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK3)
    | r2_hidden(k4_tarski(sK49(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5)),sK50(sK3,k8_relat_1(sK4,sK5),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))),k8_relat_1(k3_xboole_0(sK3,sK4),sK5))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK3,sK4),sK5))
    | ~ v1_relat_1(k8_relat_1(sK4,sK5)) ),
    inference(resolution,[],[f3387,f3229])).

fof(f3387,plain,(
    ! [X2,X0,X1] :
      ( sQ152_eqProxy(k8_relat_1(X0,X1),X2)
      | r2_hidden(sK50(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f2127,f3211])).

fof(f2127,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(sK50(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK49(X0,X1,X2),sK50(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1470])).

fof(f4267,plain,(
    spl153_3 ),
    inference(avatar_contradiction_clause,[],[f4266])).

fof(f4266,plain,
    ( $false
    | spl153_3 ),
    inference(subsumption_resolution,[],[f4262,f1791])).

fof(f4262,plain,
    ( ~ v1_relat_1(sK5)
    | spl153_3 ),
    inference(resolution,[],[f4250,f2080])).

fof(f4250,plain,
    ( ~ v1_relat_1(k8_relat_1(sK4,sK5))
    | spl153_3 ),
    inference(avatar_component_clause,[],[f4248])).
%------------------------------------------------------------------------------
