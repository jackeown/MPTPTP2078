%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t148_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:16 EDT 2019

% Result     : Theorem 93.84s
% Output     : Refutation 93.84s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 296 expanded)
%              Number of leaves         :   21 (  93 expanded)
%              Depth                    :   13
%              Number of atoms          :  492 (1541 expanded)
%              Number of equality atoms :   74 ( 346 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8952,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f267,f296,f715,f721,f742,f8873,f8928])).

fof(f8928,plain,
    ( spl10_1
    | ~ spl10_4
    | ~ spl10_10 ),
    inference(avatar_contradiction_clause,[],[f8927])).

fof(f8927,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f8926,f257])).

fof(f257,plain,
    ( ~ r2_hidden(sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl10_1
  <=> ~ r2_hidden(sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f8926,plain,
    ( r2_hidden(sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | ~ spl10_4
    | ~ spl10_10 ),
    inference(forward_demodulation,[],[f8905,f788])).

fof(f788,plain,
    ( k1_funct_1(sK1,sK5(sK1,k1_relat_1(sK1),sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))))) = sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f83,f84,f295,f135])).

fof(f135,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK5(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK5(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK3(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK4(X0,X1,X2)) = sK3(X0,X1,X2)
                  & r2_hidden(sK4(X0,X1,X2),X1)
                  & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X1,X6)) = X6
                    & r2_hidden(sK5(X0,X1,X6),X1)
                    & r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f64,f67,f66,f65])).

fof(f65,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK3(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK3(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1,X2)) = X3
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1,X6)) = X6
        & r2_hidden(sK5(X0,X1,X6),X1)
        & r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t148_funct_1.p',d12_funct_1)).

fof(f295,plain,
    ( r2_hidden(sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl10_4
  <=> r2_hidden(sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f84,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f56])).

fof(f56,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t148_funct_1.p',t148_funct_1)).

fof(f83,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f8905,plain,
    ( r2_hidden(k1_funct_1(sK1,sK5(sK1,k1_relat_1(sK1),sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))))),k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | ~ spl10_4
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f83,f84,f787,f5421,f134])).

fof(f134,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f133])).

fof(f133,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f5421,plain,
    ( r2_hidden(sK5(sK1,k1_relat_1(sK1),sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),k10_relat_1(sK1,sK0))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f5420])).

fof(f5420,plain,
    ( spl10_10
  <=> r2_hidden(sK5(sK1,k1_relat_1(sK1),sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),k10_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f787,plain,
    ( r2_hidden(sK5(sK1,k1_relat_1(sK1),sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),k1_relat_1(sK1))
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f83,f84,f295,f136])).

fof(f136,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f8873,plain,
    ( ~ spl10_2
    | ~ spl10_4
    | spl10_11 ),
    inference(avatar_contradiction_clause,[],[f8872])).

fof(f8872,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f8871,f266])).

fof(f266,plain,
    ( r2_hidden(sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl10_2
  <=> r2_hidden(sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f8871,plain,
    ( ~ r2_hidden(sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),sK0)
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(forward_demodulation,[],[f8852,f788])).

fof(f8852,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK5(sK1,k1_relat_1(sK1),sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))))),sK0)
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(unit_resulting_resolution,[],[f83,f84,f787,f5424,f130])).

fof(f130,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1)
                | ~ r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1)
                  & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f60,f61])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1)
            & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t148_funct_1.p',d13_funct_1)).

fof(f5424,plain,
    ( ~ r2_hidden(sK5(sK1,k1_relat_1(sK1),sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),k10_relat_1(sK1,sK0))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f5423])).

fof(f5423,plain,
    ( spl10_11
  <=> ~ r2_hidden(sK5(sK1,k1_relat_1(sK1),sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),k10_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f742,plain,
    ( spl10_2
    | ~ spl10_0 ),
    inference(avatar_split_clause,[],[f685,f259,f265])).

fof(f259,plain,
    ( spl10_0
  <=> r2_hidden(sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f685,plain,
    ( r2_hidden(sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),sK0)
    | ~ spl10_0 ),
    inference(unit_resulting_resolution,[],[f146,f260,f114])).

fof(f114,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f74,f75])).

fof(f75,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t148_funct_1.p',d3_tarski)).

fof(f260,plain,
    ( r2_hidden(sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f259])).

fof(f146,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f83,f84,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t148_funct_1.p',t145_funct_1)).

fof(f721,plain,
    ( spl10_4
    | ~ spl10_0 ),
    inference(avatar_split_clause,[],[f688,f259,f294])).

fof(f688,plain,
    ( r2_hidden(sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl10_0 ),
    inference(unit_resulting_resolution,[],[f145,f260,f114])).

fof(f145,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,k1_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f83,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t148_funct_1.p',t147_relat_1)).

fof(f715,plain,
    ( ~ spl10_5
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f702,f265,f259,f291])).

fof(f291,plain,
    ( spl10_5
  <=> ~ r2_hidden(sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f702,plain,
    ( ~ r2_hidden(sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f85,f266,f260,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK8(X0,X1,X2),X1)
      | ~ r2_hidden(sK8(X0,X1,X2),X0)
      | ~ r2_hidden(sK8(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
            | ~ r2_hidden(sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK8(X0,X1,X2),X1)
              & r2_hidden(sK8(X0,X1,X2),X0) )
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f80,f81])).

fof(f81,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
          | ~ r2_hidden(sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(sK8(X0,X1,X2),X0) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
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
    inference(rectify,[],[f79])).

fof(f79,plain,(
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
    inference(flattening,[],[f78])).

fof(f78,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t148_funct_1.p',d4_xboole_0)).

fof(f85,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f57])).

fof(f296,plain,
    ( spl10_0
    | spl10_4 ),
    inference(avatar_split_clause,[],[f275,f294,f259])).

fof(f275,plain,
    ( r2_hidden(sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k1_relat_1(sK1)))
    | r2_hidden(sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(equality_resolution,[],[f152])).

fof(f152,plain,(
    ! [X1] :
      ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != X1
      | r2_hidden(sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),X1),k9_relat_1(sK1,k1_relat_1(sK1)))
      | r2_hidden(sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),X1),X1) ) ),
    inference(superposition,[],[f85,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK8(X0,X1,X2),X1)
      | r2_hidden(sK8(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f267,plain,
    ( spl10_0
    | spl10_2 ),
    inference(avatar_split_clause,[],[f240,f265,f259])).

fof(f240,plain,
    ( r2_hidden(sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),sK0)
    | r2_hidden(sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(equality_resolution,[],[f151])).

fof(f151,plain,(
    ! [X0] :
      ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != X0
      | r2_hidden(sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),X0),sK0)
      | r2_hidden(sK8(sK0,k9_relat_1(sK1,k1_relat_1(sK1)),X0),X0) ) ),
    inference(superposition,[],[f85,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK8(X0,X1,X2),X0)
      | r2_hidden(sK8(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f82])).
%------------------------------------------------------------------------------
