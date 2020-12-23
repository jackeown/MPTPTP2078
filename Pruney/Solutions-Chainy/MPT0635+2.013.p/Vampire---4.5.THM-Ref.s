%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:20 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 140 expanded)
%              Number of leaves         :   24 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  319 ( 438 expanded)
%              Number of equality atoms :   89 ( 126 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f182,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f123,f125,f127,f129,f177,f181])).

fof(f181,plain,
    ( spl7_5
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f140,f119])).

fof(f119,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl7_6
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f140,plain,
    ( ~ r2_hidden(sK2,sK3)
    | spl7_5 ),
    inference(trivial_inequality_removal,[],[f139])).

fof(f139,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(sK4,sK2)
    | ~ r2_hidden(sK2,sK3)
    | spl7_5 ),
    inference(superposition,[],[f116,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).

fof(f116,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(sK4,k1_funct_1(k6_relat_1(sK3),sK2))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl7_5
  <=> k1_funct_1(sK4,sK2) = k1_funct_1(sK4,k1_funct_1(k6_relat_1(sK3),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f177,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl7_6 ),
    inference(resolution,[],[f163,f78])).

fof(f78,plain,(
    ! [X4,X2,X5,X3,X1] : sP0(X3,X1,X2,X3,X4,X5) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5)
      | X0 != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X6,X4,X3,X2,X1,X0] :
      ( ( sP0(X6,X4,X3,X2,X1,X0)
        | ( X4 != X6
          & X3 != X6
          & X2 != X6
          & X1 != X6
          & X0 != X6 ) )
      & ( X4 = X6
        | X3 = X6
        | X2 = X6
        | X1 = X6
        | X0 = X6
        | ~ sP0(X6,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X6,X4,X3,X2,X1,X0] :
      ( ( sP0(X6,X4,X3,X2,X1,X0)
        | ( X4 != X6
          & X3 != X6
          & X2 != X6
          & X1 != X6
          & X0 != X6 ) )
      & ( X4 = X6
        | X3 = X6
        | X2 = X6
        | X1 = X6
        | X0 = X6
        | ~ sP0(X6,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X6,X4,X3,X2,X1,X0] :
      ( sP0(X6,X4,X3,X2,X1,X0)
    <=> ( X4 = X6
        | X3 = X6
        | X2 = X6
        | X1 = X6
        | X0 = X6 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f163,plain,
    ( ~ sP0(sK3,k1_relat_1(sK4),k1_relat_1(sK4),sK3,sK3,sK3)
    | spl7_6 ),
    inference(resolution,[],[f161,f82])).

fof(f82,plain,(
    r2_hidden(sK2,k1_setfam_1(k3_enumset1(sK3,sK3,sK3,k1_relat_1(sK4),k1_relat_1(sK4)))) ),
    inference(backward_demodulation,[],[f74,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f56,f71,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

fof(f74,plain,(
    r2_hidden(sK2,k1_setfam_1(k3_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),sK3))) ),
    inference(definition_unfolding,[],[f42,f73])).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f71])).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f42,plain,(
    r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2)
    & r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3))
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
        & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK4,sK2) != k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2)
      & r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3))
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

fof(f161,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ r2_hidden(sK2,k1_setfam_1(k3_enumset1(X4,X3,X2,X1,X0)))
        | ~ sP0(sK3,X0,X1,X2,X3,X4) )
    | spl7_6 ),
    inference(resolution,[],[f134,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : sP1(X0,X1,X2,X3,X4,k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ~ sP1(X0,X1,X2,X3,X4,X5) )
      & ( sP1(X0,X1,X2,X3,X4,X5)
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> sP1(X0,X1,X2,X3,X4,X5) ) ),
    inference(definition_folding,[],[f22,f24,f23])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( sP1(X0,X1,X2,X3,X4,X5)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> sP0(X6,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

fof(f134,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ sP1(X5,X4,X3,X2,X1,X0)
        | ~ sP0(sK3,X1,X2,X3,X4,X5)
        | ~ r2_hidden(sK2,k1_setfam_1(X0)) )
    | spl7_6 ),
    inference(resolution,[],[f132,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | ~ sP0(X7,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP1(X0,X1,X2,X3,X4,X5)
        | ( ( ~ sP0(sK6(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK6(X0,X1,X2,X3,X4,X5),X5) )
          & ( sP0(sK6(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
            | r2_hidden(sK6(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ~ sP0(X7,X4,X3,X2,X1,X0) )
            & ( sP0(X7,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f34])).

fof(f34,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ~ sP0(X6,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X6,X5) )
          & ( sP0(X6,X4,X3,X2,X1,X0)
            | r2_hidden(X6,X5) ) )
     => ( ( ~ sP0(sK6(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK6(X0,X1,X2,X3,X4,X5),X5) )
        & ( sP0(sK6(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
          | r2_hidden(sK6(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP1(X0,X1,X2,X3,X4,X5)
        | ? [X6] :
            ( ( ~ sP0(X6,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X5) )
            & ( sP0(X6,X4,X3,X2,X1,X0)
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ~ sP0(X7,X4,X3,X2,X1,X0) )
            & ( sP0(X7,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP1(X0,X1,X2,X3,X4,X5)
        | ? [X6] :
            ( ( ~ sP0(X6,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X5) )
            & ( sP0(X6,X4,X3,X2,X1,X0)
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ~ sP0(X6,X4,X3,X2,X1,X0) )
            & ( sP0(X6,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | ~ r2_hidden(sK2,k1_setfam_1(X0)) )
    | spl7_6 ),
    inference(resolution,[],[f131,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f131,plain,
    ( ! [X5] :
        ( ~ r1_tarski(X5,sK3)
        | ~ r2_hidden(sK2,X5) )
    | spl7_6 ),
    inference(resolution,[],[f120,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f120,plain,
    ( ~ r2_hidden(sK2,sK3)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f118])).

fof(f129,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl7_2 ),
    inference(resolution,[],[f104,f45])).

fof(f45,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f104,plain,
    ( ~ v1_funct_1(k6_relat_1(sK3))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl7_2
  <=> v1_funct_1(k6_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f127,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl7_1 ),
    inference(resolution,[],[f100,f44])).

fof(f44,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f100,plain,
    ( ~ v1_relat_1(k6_relat_1(sK3))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl7_1
  <=> v1_relat_1(k6_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f125,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl7_4 ),
    inference(resolution,[],[f112,f41])).

fof(f41,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f112,plain,
    ( ~ v1_funct_1(sK4)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl7_4
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f123,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl7_3 ),
    inference(resolution,[],[f108,f40])).

fof(f40,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f108,plain,
    ( ~ v1_relat_1(sK4)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl7_3
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f121,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f96,f118,f114,f110,f106,f102,f98])).

fof(f96,plain,
    ( ~ r2_hidden(sK2,sK3)
    | k1_funct_1(sK4,sK2) != k1_funct_1(sK4,k1_funct_1(k6_relat_1(sK3),sK2))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(k6_relat_1(sK3))
    | ~ v1_relat_1(k6_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f95,f46])).

fof(f46,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f95,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(sK4,k1_funct_1(k6_relat_1(sK3),sK2))
    | ~ r2_hidden(sK2,k1_relat_1(k6_relat_1(sK3)))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(k6_relat_1(sK3))
    | ~ v1_relat_1(k6_relat_1(sK3)) ),
    inference(superposition,[],[f43,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(f43,plain,(
    k1_funct_1(sK4,sK2) != k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n005.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:10:02 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.55  % (13123)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.32/0.55  % (13125)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.56  % (13125)Refutation found. Thanks to Tanya!
% 1.32/0.56  % SZS status Theorem for theBenchmark
% 1.32/0.56  % (13139)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.32/0.56  % (13117)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.32/0.56  % (13131)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.32/0.57  % (13123)Refutation not found, incomplete strategy% (13123)------------------------------
% 1.32/0.57  % (13123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.57  % (13123)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.57  
% 1.32/0.57  % (13123)Memory used [KB]: 10618
% 1.32/0.57  % (13123)Time elapsed: 0.135 s
% 1.32/0.57  % (13123)------------------------------
% 1.32/0.57  % (13123)------------------------------
% 1.32/0.57  % (13116)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.60/0.57  % (13119)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.60/0.57  % (13135)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.60/0.57  % SZS output start Proof for theBenchmark
% 1.60/0.57  fof(f182,plain,(
% 1.60/0.57    $false),
% 1.60/0.57    inference(avatar_sat_refutation,[],[f121,f123,f125,f127,f129,f177,f181])).
% 1.60/0.57  fof(f181,plain,(
% 1.60/0.57    spl7_5 | ~spl7_6),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f178])).
% 1.60/0.57  fof(f178,plain,(
% 1.60/0.57    $false | (spl7_5 | ~spl7_6)),
% 1.60/0.57    inference(resolution,[],[f140,f119])).
% 1.60/0.57  fof(f119,plain,(
% 1.60/0.57    r2_hidden(sK2,sK3) | ~spl7_6),
% 1.60/0.57    inference(avatar_component_clause,[],[f118])).
% 1.60/0.57  fof(f118,plain,(
% 1.60/0.57    spl7_6 <=> r2_hidden(sK2,sK3)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.60/0.57  fof(f140,plain,(
% 1.60/0.57    ~r2_hidden(sK2,sK3) | spl7_5),
% 1.60/0.57    inference(trivial_inequality_removal,[],[f139])).
% 1.60/0.57  fof(f139,plain,(
% 1.60/0.57    k1_funct_1(sK4,sK2) != k1_funct_1(sK4,sK2) | ~r2_hidden(sK2,sK3) | spl7_5),
% 1.60/0.57    inference(superposition,[],[f116,f51])).
% 1.60/0.57  fof(f51,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f18])).
% 1.60/0.57  fof(f18,plain,(
% 1.60/0.57    ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1))),
% 1.60/0.57    inference(ennf_transformation,[],[f12])).
% 1.60/0.57  fof(f12,axiom,(
% 1.60/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => k1_funct_1(k6_relat_1(X1),X0) = X0)),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).
% 1.60/0.57  fof(f116,plain,(
% 1.60/0.57    k1_funct_1(sK4,sK2) != k1_funct_1(sK4,k1_funct_1(k6_relat_1(sK3),sK2)) | spl7_5),
% 1.60/0.57    inference(avatar_component_clause,[],[f114])).
% 1.60/0.57  fof(f114,plain,(
% 1.60/0.57    spl7_5 <=> k1_funct_1(sK4,sK2) = k1_funct_1(sK4,k1_funct_1(k6_relat_1(sK3),sK2))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.60/0.57  fof(f177,plain,(
% 1.60/0.57    spl7_6),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f171])).
% 1.60/0.57  fof(f171,plain,(
% 1.60/0.57    $false | spl7_6),
% 1.60/0.57    inference(resolution,[],[f163,f78])).
% 1.60/0.57  fof(f78,plain,(
% 1.60/0.57    ( ! [X4,X2,X5,X3,X1] : (sP0(X3,X1,X2,X3,X4,X5)) )),
% 1.60/0.57    inference(equality_resolution,[],[f66])).
% 1.60/0.57  fof(f66,plain,(
% 1.60/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5) | X0 != X3) )),
% 1.60/0.57    inference(cnf_transformation,[],[f38])).
% 1.60/0.57  fof(f38,plain,(
% 1.60/0.57    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 1.60/0.57    inference(rectify,[],[f37])).
% 1.60/0.57  fof(f37,plain,(
% 1.60/0.57    ! [X6,X4,X3,X2,X1,X0] : ((sP0(X6,X4,X3,X2,X1,X0) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~sP0(X6,X4,X3,X2,X1,X0)))),
% 1.60/0.57    inference(flattening,[],[f36])).
% 1.60/0.57  fof(f36,plain,(
% 1.60/0.57    ! [X6,X4,X3,X2,X1,X0] : ((sP0(X6,X4,X3,X2,X1,X0) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~sP0(X6,X4,X3,X2,X1,X0)))),
% 1.60/0.57    inference(nnf_transformation,[],[f23])).
% 1.60/0.57  fof(f23,plain,(
% 1.60/0.57    ! [X6,X4,X3,X2,X1,X0] : (sP0(X6,X4,X3,X2,X1,X0) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6))),
% 1.60/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.60/0.57  fof(f163,plain,(
% 1.60/0.57    ~sP0(sK3,k1_relat_1(sK4),k1_relat_1(sK4),sK3,sK3,sK3) | spl7_6),
% 1.60/0.57    inference(resolution,[],[f161,f82])).
% 1.60/0.57  fof(f82,plain,(
% 1.60/0.57    r2_hidden(sK2,k1_setfam_1(k3_enumset1(sK3,sK3,sK3,k1_relat_1(sK4),k1_relat_1(sK4))))),
% 1.60/0.57    inference(backward_demodulation,[],[f74,f75])).
% 1.60/0.57  fof(f75,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X1,X0)) )),
% 1.60/0.57    inference(definition_unfolding,[],[f56,f71,f71])).
% 1.60/0.57  fof(f71,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.60/0.57    inference(definition_unfolding,[],[f57,f58])).
% 1.60/0.57  fof(f58,plain,(
% 1.60/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f5])).
% 1.60/0.57  fof(f5,axiom,(
% 1.60/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.60/0.57  fof(f57,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f4])).
% 1.60/0.57  fof(f4,axiom,(
% 1.60/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.60/0.57  fof(f56,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f2])).
% 1.60/0.57  fof(f2,axiom,(
% 1.60/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).
% 1.60/0.57  fof(f74,plain,(
% 1.60/0.57    r2_hidden(sK2,k1_setfam_1(k3_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),sK3)))),
% 1.60/0.57    inference(definition_unfolding,[],[f42,f73])).
% 1.60/0.57  fof(f73,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.60/0.57    inference(definition_unfolding,[],[f48,f72])).
% 1.60/0.57  fof(f72,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.60/0.57    inference(definition_unfolding,[],[f49,f71])).
% 1.60/0.57  fof(f49,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f3])).
% 1.60/0.57  fof(f3,axiom,(
% 1.60/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.60/0.57  fof(f48,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f7])).
% 1.60/0.57  fof(f7,axiom,(
% 1.60/0.57    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.60/0.57  fof(f42,plain,(
% 1.60/0.57    r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3))),
% 1.60/0.57    inference(cnf_transformation,[],[f27])).
% 1.60/0.57  fof(f27,plain,(
% 1.60/0.57    k1_funct_1(sK4,sK2) != k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) & r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 1.60/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f26])).
% 1.60/0.57  fof(f26,plain,(
% 1.60/0.57    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK4,sK2) != k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2) & r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 1.60/0.57    introduced(choice_axiom,[])).
% 1.60/0.57  fof(f16,plain,(
% 1.60/0.57    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.60/0.57    inference(flattening,[],[f15])).
% 1.60/0.57  fof(f15,plain,(
% 1.60/0.57    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.60/0.57    inference(ennf_transformation,[],[f14])).
% 1.60/0.57  fof(f14,negated_conjecture,(
% 1.60/0.57    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 1.60/0.57    inference(negated_conjecture,[],[f13])).
% 1.60/0.57  fof(f13,conjecture,(
% 1.60/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).
% 1.60/0.57  fof(f161,plain,(
% 1.60/0.57    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(sK2,k1_setfam_1(k3_enumset1(X4,X3,X2,X1,X0))) | ~sP0(sK3,X0,X1,X2,X3,X4)) ) | spl7_6),
% 1.60/0.57    inference(resolution,[],[f134,f81])).
% 1.60/0.57  fof(f81,plain,(
% 1.60/0.57    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,X4,k3_enumset1(X0,X1,X2,X3,X4))) )),
% 1.60/0.57    inference(equality_resolution,[],[f69])).
% 1.60/0.57  fof(f69,plain,(
% 1.60/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 1.60/0.57    inference(cnf_transformation,[],[f39])).
% 1.60/0.57  fof(f39,plain,(
% 1.60/0.57    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ~sP1(X0,X1,X2,X3,X4,X5)) & (sP1(X0,X1,X2,X3,X4,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 1.60/0.57    inference(nnf_transformation,[],[f25])).
% 1.60/0.57  fof(f25,plain,(
% 1.60/0.57    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> sP1(X0,X1,X2,X3,X4,X5))),
% 1.60/0.57    inference(definition_folding,[],[f22,f24,f23])).
% 1.60/0.57  fof(f24,plain,(
% 1.60/0.57    ! [X0,X1,X2,X3,X4,X5] : (sP1(X0,X1,X2,X3,X4,X5) <=> ! [X6] : (r2_hidden(X6,X5) <=> sP0(X6,X4,X3,X2,X1,X0)))),
% 1.60/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.60/0.57  fof(f22,plain,(
% 1.60/0.57    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 1.60/0.57    inference(ennf_transformation,[],[f6])).
% 1.60/0.57  fof(f6,axiom,(
% 1.60/0.57    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).
% 1.60/0.57  fof(f134,plain,(
% 1.60/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~sP1(X5,X4,X3,X2,X1,X0) | ~sP0(sK3,X1,X2,X3,X4,X5) | ~r2_hidden(sK2,k1_setfam_1(X0))) ) | spl7_6),
% 1.60/0.57    inference(resolution,[],[f132,f60])).
% 1.60/0.57  fof(f60,plain,(
% 1.60/0.57    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | ~sP0(X7,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f35])).
% 1.60/0.57  fof(f35,plain,(
% 1.60/0.57    ! [X0,X1,X2,X3,X4,X5] : ((sP1(X0,X1,X2,X3,X4,X5) | ((~sP0(sK6(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | ~r2_hidden(sK6(X0,X1,X2,X3,X4,X5),X5)) & (sP0(sK6(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | r2_hidden(sK6(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | ~sP0(X7,X4,X3,X2,X1,X0)) & (sP0(X7,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X5))) | ~sP1(X0,X1,X2,X3,X4,X5)))),
% 1.60/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f34])).
% 1.60/0.57  fof(f34,plain,(
% 1.60/0.57    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : ((~sP0(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5)) & (sP0(X6,X4,X3,X2,X1,X0) | r2_hidden(X6,X5))) => ((~sP0(sK6(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | ~r2_hidden(sK6(X0,X1,X2,X3,X4,X5),X5)) & (sP0(sK6(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | r2_hidden(sK6(X0,X1,X2,X3,X4,X5),X5))))),
% 1.60/0.57    introduced(choice_axiom,[])).
% 1.60/0.57  fof(f33,plain,(
% 1.60/0.57    ! [X0,X1,X2,X3,X4,X5] : ((sP1(X0,X1,X2,X3,X4,X5) | ? [X6] : ((~sP0(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5)) & (sP0(X6,X4,X3,X2,X1,X0) | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | ~sP0(X7,X4,X3,X2,X1,X0)) & (sP0(X7,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X5))) | ~sP1(X0,X1,X2,X3,X4,X5)))),
% 1.60/0.57    inference(rectify,[],[f32])).
% 1.60/0.57  fof(f32,plain,(
% 1.60/0.57    ! [X0,X1,X2,X3,X4,X5] : ((sP1(X0,X1,X2,X3,X4,X5) | ? [X6] : ((~sP0(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5)) & (sP0(X6,X4,X3,X2,X1,X0) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | ~sP0(X6,X4,X3,X2,X1,X0)) & (sP0(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5))) | ~sP1(X0,X1,X2,X3,X4,X5)))),
% 1.60/0.57    inference(nnf_transformation,[],[f24])).
% 1.60/0.57  fof(f132,plain,(
% 1.60/0.57    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r2_hidden(sK2,k1_setfam_1(X0))) ) | spl7_6),
% 1.60/0.57    inference(resolution,[],[f131,f50])).
% 1.60/0.57  fof(f50,plain,(
% 1.60/0.57    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f17])).
% 1.60/0.57  fof(f17,plain,(
% 1.60/0.57    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 1.60/0.57    inference(ennf_transformation,[],[f8])).
% 1.60/0.57  fof(f8,axiom,(
% 1.60/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 1.60/0.57  fof(f131,plain,(
% 1.60/0.57    ( ! [X5] : (~r1_tarski(X5,sK3) | ~r2_hidden(sK2,X5)) ) | spl7_6),
% 1.60/0.57    inference(resolution,[],[f120,f53])).
% 1.60/0.57  fof(f53,plain,(
% 1.60/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f31])).
% 1.60/0.57  fof(f31,plain,(
% 1.60/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.60/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).
% 1.60/0.57  fof(f30,plain,(
% 1.60/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.60/0.57    introduced(choice_axiom,[])).
% 1.60/0.57  fof(f29,plain,(
% 1.60/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.60/0.57    inference(rectify,[],[f28])).
% 1.60/0.57  fof(f28,plain,(
% 1.60/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.60/0.57    inference(nnf_transformation,[],[f21])).
% 1.60/0.57  fof(f21,plain,(
% 1.60/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.60/0.57    inference(ennf_transformation,[],[f1])).
% 1.60/0.57  fof(f1,axiom,(
% 1.60/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.60/0.57  fof(f120,plain,(
% 1.60/0.57    ~r2_hidden(sK2,sK3) | spl7_6),
% 1.60/0.57    inference(avatar_component_clause,[],[f118])).
% 1.60/0.57  fof(f129,plain,(
% 1.60/0.57    spl7_2),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f128])).
% 1.60/0.57  fof(f128,plain,(
% 1.60/0.57    $false | spl7_2),
% 1.60/0.57    inference(resolution,[],[f104,f45])).
% 1.60/0.57  fof(f45,plain,(
% 1.60/0.57    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f10])).
% 1.60/0.57  fof(f10,axiom,(
% 1.60/0.57    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.60/0.57  fof(f104,plain,(
% 1.60/0.57    ~v1_funct_1(k6_relat_1(sK3)) | spl7_2),
% 1.60/0.57    inference(avatar_component_clause,[],[f102])).
% 1.60/0.57  fof(f102,plain,(
% 1.60/0.57    spl7_2 <=> v1_funct_1(k6_relat_1(sK3))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.60/0.57  fof(f127,plain,(
% 1.60/0.57    spl7_1),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f126])).
% 1.60/0.57  fof(f126,plain,(
% 1.60/0.57    $false | spl7_1),
% 1.60/0.57    inference(resolution,[],[f100,f44])).
% 1.60/0.57  fof(f44,plain,(
% 1.60/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f10])).
% 1.60/0.57  fof(f100,plain,(
% 1.60/0.57    ~v1_relat_1(k6_relat_1(sK3)) | spl7_1),
% 1.60/0.57    inference(avatar_component_clause,[],[f98])).
% 1.60/0.57  fof(f98,plain,(
% 1.60/0.57    spl7_1 <=> v1_relat_1(k6_relat_1(sK3))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.60/0.57  fof(f125,plain,(
% 1.60/0.57    spl7_4),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f124])).
% 1.60/0.57  fof(f124,plain,(
% 1.60/0.57    $false | spl7_4),
% 1.60/0.57    inference(resolution,[],[f112,f41])).
% 1.60/0.57  fof(f41,plain,(
% 1.60/0.57    v1_funct_1(sK4)),
% 1.60/0.57    inference(cnf_transformation,[],[f27])).
% 1.60/0.57  fof(f112,plain,(
% 1.60/0.57    ~v1_funct_1(sK4) | spl7_4),
% 1.60/0.57    inference(avatar_component_clause,[],[f110])).
% 1.60/0.57  fof(f110,plain,(
% 1.60/0.57    spl7_4 <=> v1_funct_1(sK4)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.60/0.57  fof(f123,plain,(
% 1.60/0.57    spl7_3),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f122])).
% 1.60/0.57  fof(f122,plain,(
% 1.60/0.57    $false | spl7_3),
% 1.60/0.57    inference(resolution,[],[f108,f40])).
% 1.60/0.57  fof(f40,plain,(
% 1.60/0.57    v1_relat_1(sK4)),
% 1.60/0.57    inference(cnf_transformation,[],[f27])).
% 1.60/0.57  fof(f108,plain,(
% 1.60/0.57    ~v1_relat_1(sK4) | spl7_3),
% 1.60/0.57    inference(avatar_component_clause,[],[f106])).
% 1.60/0.57  fof(f106,plain,(
% 1.60/0.57    spl7_3 <=> v1_relat_1(sK4)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.60/0.57  fof(f121,plain,(
% 1.60/0.57    ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6),
% 1.60/0.57    inference(avatar_split_clause,[],[f96,f118,f114,f110,f106,f102,f98])).
% 1.60/0.57  fof(f96,plain,(
% 1.60/0.57    ~r2_hidden(sK2,sK3) | k1_funct_1(sK4,sK2) != k1_funct_1(sK4,k1_funct_1(k6_relat_1(sK3),sK2)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(k6_relat_1(sK3)) | ~v1_relat_1(k6_relat_1(sK3))),
% 1.60/0.57    inference(forward_demodulation,[],[f95,f46])).
% 1.60/0.57  fof(f46,plain,(
% 1.60/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.60/0.57    inference(cnf_transformation,[],[f9])).
% 1.60/0.57  fof(f9,axiom,(
% 1.60/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.60/0.57  fof(f95,plain,(
% 1.60/0.57    k1_funct_1(sK4,sK2) != k1_funct_1(sK4,k1_funct_1(k6_relat_1(sK3),sK2)) | ~r2_hidden(sK2,k1_relat_1(k6_relat_1(sK3))) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(k6_relat_1(sK3)) | ~v1_relat_1(k6_relat_1(sK3))),
% 1.60/0.57    inference(superposition,[],[f43,f52])).
% 1.60/0.57  fof(f52,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f20])).
% 1.60/0.57  fof(f20,plain,(
% 1.60/0.57    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.60/0.57    inference(flattening,[],[f19])).
% 1.60/0.57  fof(f19,plain,(
% 1.60/0.57    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.60/0.57    inference(ennf_transformation,[],[f11])).
% 1.60/0.57  fof(f11,axiom,(
% 1.60/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
% 1.60/0.57  fof(f43,plain,(
% 1.60/0.57    k1_funct_1(sK4,sK2) != k1_funct_1(k5_relat_1(k6_relat_1(sK3),sK4),sK2)),
% 1.60/0.57    inference(cnf_transformation,[],[f27])).
% 1.60/0.57  % SZS output end Proof for theBenchmark
% 1.60/0.57  % (13125)------------------------------
% 1.60/0.57  % (13125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (13125)Termination reason: Refutation
% 1.60/0.57  
% 1.60/0.57  % (13125)Memory used [KB]: 6268
% 1.60/0.57  % (13125)Time elapsed: 0.128 s
% 1.60/0.57  % (13125)------------------------------
% 1.60/0.57  % (13125)------------------------------
% 1.60/0.58  % (13112)Success in time 0.213 s
%------------------------------------------------------------------------------
