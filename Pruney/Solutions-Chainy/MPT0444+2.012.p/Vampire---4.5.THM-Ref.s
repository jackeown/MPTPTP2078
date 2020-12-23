%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:02 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 215 expanded)
%              Number of leaves         :   26 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  296 ( 487 expanded)
%              Number of equality atoms :   70 ( 148 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f109,f112,f116,f125,f134,f137,f147])).

fof(f147,plain,(
    spl5_7 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl5_7 ),
    inference(resolution,[],[f145,f78])).

fof(f78,plain,(
    ! [X4,X2,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X6,X4,X3,X2,X1,X0] :
      ( sP0(X6,X4,X3,X2,X1,X0)
    <=> ( X4 = X6
        | X3 = X6
        | X2 = X6
        | X1 = X6
        | X0 = X6 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f145,plain,
    ( ~ sP0(sK3,sK3,sK2,sK2,sK2,sK2)
    | spl5_7 ),
    inference(resolution,[],[f139,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] : sP1(X0,X1,X2,X3,X4,k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5)
      | k5_enumset1(X0,X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f66,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ~ sP1(X0,X1,X2,X3,X4,X5) )
      & ( sP1(X0,X1,X2,X3,X4,X5)
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> sP1(X0,X1,X2,X3,X4,X5) ) ),
    inference(definition_folding,[],[f23,f25,f24])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( sP1(X0,X1,X2,X3,X4,X5)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> sP0(X6,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f139,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ sP1(X4,X3,X2,X1,X0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
        | ~ sP0(sK3,X0,X1,X2,X3,X4) )
    | spl5_7 ),
    inference(resolution,[],[f138,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | ~ sP0(X7,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP1(X0,X1,X2,X3,X4,X5)
        | ( ( ~ sP0(sK4(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5) )
          & ( sP0(sK4(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
            | r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ~ sP0(X7,X4,X3,X2,X1,X0) )
            & ( sP0(X7,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ~ sP0(X6,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X6,X5) )
          & ( sP0(X6,X4,X3,X2,X1,X0)
            | r2_hidden(X6,X5) ) )
     => ( ( ~ sP0(sK4(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5) )
        & ( sP0(sK4(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0)
          | r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f25])).

% (31719)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f138,plain,
    ( ~ r2_hidden(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | spl5_7 ),
    inference(resolution,[],[f133,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f133,plain,
    ( ~ r1_tarski(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)),sK3)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl5_7
  <=> r1_tarski(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f137,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl5_6 ),
    inference(resolution,[],[f129,f40])).

fof(f40,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK2,sK3)),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3)))
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK2,X1)),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK2,X1)),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK2,sK3)),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3)))
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

fof(f129,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl5_6
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f134,plain,
    ( ~ spl5_3
    | ~ spl5_6
    | ~ spl5_7
    | spl5_2 ),
    inference(avatar_split_clause,[],[f117,f92,f131,f127,f98])).

fof(f98,plain,
    ( spl5_3
  <=> v1_relat_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f92,plain,
    ( spl5_2
  <=> r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f117,plain,
    ( ~ r1_tarski(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)),sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)))
    | spl5_2 ),
    inference(resolution,[],[f94,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f94,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),k2_relat_1(sK3))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f125,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl5_3 ),
    inference(resolution,[],[f120,f74])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f45,f72])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f53,f68])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f120,plain,
    ( ~ r1_tarski(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)),sK2)
    | spl5_3 ),
    inference(resolution,[],[f118,f39])).

fof(f39,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)),X0) )
    | spl5_3 ),
    inference(resolution,[],[f113,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f113,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)),k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl5_3 ),
    inference(resolution,[],[f100,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f100,plain,
    ( ~ v1_relat_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f116,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl5_5 ),
    inference(resolution,[],[f108,f74])).

fof(f108,plain,
    ( ~ r1_tarski(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)),sK2)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl5_5
  <=> r1_tarski(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f112,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | spl5_4 ),
    inference(resolution,[],[f104,f39])).

fof(f104,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f102])).

% (31694)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f102,plain,
    ( spl5_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f109,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f96,f88,f106,f102,f98])).

fof(f88,plain,
    ( spl5_1
  <=> r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f96,plain,
    ( ~ r1_tarski(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)))
    | spl5_1 ),
    inference(resolution,[],[f90,f43])).

fof(f90,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),k2_relat_1(sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f95,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f86,f92,f88])).

fof(f86,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),k2_relat_1(sK3))
    | ~ r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),k2_relat_1(sK2)) ),
    inference(resolution,[],[f75,f73])).

fof(f73,plain,(
    ~ r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),k1_setfam_1(k5_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK3)))) ),
    inference(definition_unfolding,[],[f41,f72,f72])).

fof(f41,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK2,sK3)),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3))) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f72])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n010.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 14:40:14 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.47  % (31703)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.48  % (31693)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.49  % (31696)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.49  % (31721)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.50  % (31704)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.50  % (31704)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % (31699)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.51  % (31692)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.51  % (31692)Refutation not found, incomplete strategy% (31692)------------------------------
% 0.19/0.51  % (31692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (31692)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (31692)Memory used [KB]: 1663
% 0.19/0.51  % (31692)Time elapsed: 0.114 s
% 0.19/0.51  % (31692)------------------------------
% 0.19/0.51  % (31692)------------------------------
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  fof(f148,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(avatar_sat_refutation,[],[f95,f109,f112,f116,f125,f134,f137,f147])).
% 0.19/0.51  fof(f147,plain,(
% 0.19/0.51    spl5_7),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f146])).
% 0.19/0.51  fof(f146,plain,(
% 0.19/0.51    $false | spl5_7),
% 0.19/0.51    inference(resolution,[],[f145,f78])).
% 0.19/0.51  fof(f78,plain,(
% 0.19/0.51    ( ! [X4,X2,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5)) )),
% 0.19/0.51    inference(equality_resolution,[],[f65])).
% 0.19/0.51  fof(f65,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5) | X0 != X1) )),
% 0.19/0.51    inference(cnf_transformation,[],[f37])).
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 0.19/0.51    inference(rectify,[],[f36])).
% 0.19/0.51  fof(f36,plain,(
% 0.19/0.51    ! [X6,X4,X3,X2,X1,X0] : ((sP0(X6,X4,X3,X2,X1,X0) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~sP0(X6,X4,X3,X2,X1,X0)))),
% 0.19/0.51    inference(flattening,[],[f35])).
% 0.19/0.51  fof(f35,plain,(
% 0.19/0.51    ! [X6,X4,X3,X2,X1,X0] : ((sP0(X6,X4,X3,X2,X1,X0) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~sP0(X6,X4,X3,X2,X1,X0)))),
% 0.19/0.51    inference(nnf_transformation,[],[f24])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ! [X6,X4,X3,X2,X1,X0] : (sP0(X6,X4,X3,X2,X1,X0) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6))),
% 0.19/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.19/0.51  fof(f145,plain,(
% 0.19/0.51    ~sP0(sK3,sK3,sK2,sK2,sK2,sK2) | spl5_7),
% 0.19/0.51    inference(resolution,[],[f139,f83])).
% 0.19/0.51  fof(f83,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,X4,k5_enumset1(X0,X0,X0,X1,X2,X3,X4))) )),
% 0.19/0.51    inference(equality_resolution,[],[f77])).
% 0.19/0.51  fof(f77,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5) | k5_enumset1(X0,X0,X0,X1,X2,X3,X4) != X5) )),
% 0.19/0.51    inference(definition_unfolding,[],[f66,f68])).
% 0.19/0.51  fof(f68,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f54,f55])).
% 0.19/0.51  fof(f55,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f7])).
% 0.19/0.51  fof(f7,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.19/0.51  fof(f54,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.19/0.51  fof(f66,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 0.19/0.51    inference(cnf_transformation,[],[f38])).
% 0.19/0.51  fof(f38,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ~sP1(X0,X1,X2,X3,X4,X5)) & (sP1(X0,X1,X2,X3,X4,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 0.19/0.51    inference(nnf_transformation,[],[f26])).
% 0.19/0.51  fof(f26,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> sP1(X0,X1,X2,X3,X4,X5))),
% 0.19/0.51    inference(definition_folding,[],[f23,f25,f24])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4,X5] : (sP1(X0,X1,X2,X3,X4,X5) <=> ! [X6] : (r2_hidden(X6,X5) <=> sP0(X6,X4,X3,X2,X1,X0)))),
% 0.19/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 0.19/0.51    inference(ennf_transformation,[],[f8])).
% 0.19/0.51  fof(f8,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).
% 0.19/0.51  fof(f139,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X3,X1] : (~sP1(X4,X3,X2,X1,X0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | ~sP0(sK3,X0,X1,X2,X3,X4)) ) | spl5_7),
% 0.19/0.51    inference(resolution,[],[f138,f57])).
% 0.19/0.51  fof(f57,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | ~sP0(X7,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f34])).
% 0.19/0.51  fof(f34,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4,X5] : ((sP1(X0,X1,X2,X3,X4,X5) | ((~sP0(sK4(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5)) & (sP0(sK4(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | ~sP0(X7,X4,X3,X2,X1,X0)) & (sP0(X7,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X5))) | ~sP1(X0,X1,X2,X3,X4,X5)))),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : ((~sP0(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5)) & (sP0(X6,X4,X3,X2,X1,X0) | r2_hidden(X6,X5))) => ((~sP0(sK4(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5)) & (sP0(sK4(X0,X1,X2,X3,X4,X5),X4,X3,X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3,X4,X5),X5))))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f32,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4,X5] : ((sP1(X0,X1,X2,X3,X4,X5) | ? [X6] : ((~sP0(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5)) & (sP0(X6,X4,X3,X2,X1,X0) | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | ~sP0(X7,X4,X3,X2,X1,X0)) & (sP0(X7,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X5))) | ~sP1(X0,X1,X2,X3,X4,X5)))),
% 0.19/0.51    inference(rectify,[],[f31])).
% 0.19/0.51  fof(f31,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4,X5] : ((sP1(X0,X1,X2,X3,X4,X5) | ? [X6] : ((~sP0(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5)) & (sP0(X6,X4,X3,X2,X1,X0) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | ~sP0(X6,X4,X3,X2,X1,X0)) & (sP0(X6,X4,X3,X2,X1,X0) | ~r2_hidden(X6,X5))) | ~sP1(X0,X1,X2,X3,X4,X5)))),
% 0.19/0.51    inference(nnf_transformation,[],[f25])).
% 0.19/0.51  % (31719)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.51  fof(f138,plain,(
% 0.19/0.51    ~r2_hidden(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | spl5_7),
% 0.19/0.51    inference(resolution,[],[f133,f48])).
% 0.19/0.51  fof(f48,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f11])).
% 0.19/0.51  fof(f11,axiom,(
% 0.19/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.19/0.51  fof(f133,plain,(
% 0.19/0.51    ~r1_tarski(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)),sK3) | spl5_7),
% 0.19/0.51    inference(avatar_component_clause,[],[f131])).
% 0.19/0.51  fof(f131,plain,(
% 0.19/0.51    spl5_7 <=> r1_tarski(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)),sK3)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.19/0.51  fof(f137,plain,(
% 0.19/0.51    spl5_6),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f135])).
% 0.19/0.51  fof(f135,plain,(
% 0.19/0.51    $false | spl5_6),
% 0.19/0.51    inference(resolution,[],[f129,f40])).
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    v1_relat_1(sK3)),
% 0.19/0.51    inference(cnf_transformation,[],[f29])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    (~r1_tarski(k2_relat_1(k3_xboole_0(sK2,sK3)),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3))) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f28,f27])).
% 0.19/0.51  fof(f27,plain,(
% 0.19/0.51    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK2,X1)),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK2))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    ? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK2,X1)),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k3_xboole_0(sK2,sK3)),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3))) & v1_relat_1(sK3))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f15])).
% 0.19/0.51  fof(f15,negated_conjecture,(
% 0.19/0.51    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.19/0.51    inference(negated_conjecture,[],[f14])).
% 0.19/0.51  fof(f14,conjecture,(
% 0.19/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).
% 0.19/0.51  fof(f129,plain,(
% 0.19/0.51    ~v1_relat_1(sK3) | spl5_6),
% 0.19/0.51    inference(avatar_component_clause,[],[f127])).
% 0.19/0.51  fof(f127,plain,(
% 0.19/0.51    spl5_6 <=> v1_relat_1(sK3)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.19/0.51  fof(f134,plain,(
% 0.19/0.51    ~spl5_3 | ~spl5_6 | ~spl5_7 | spl5_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f117,f92,f131,f127,f98])).
% 0.19/0.51  fof(f98,plain,(
% 0.19/0.51    spl5_3 <=> v1_relat_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.51  fof(f92,plain,(
% 0.19/0.51    spl5_2 <=> r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),k2_relat_1(sK3))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.51  fof(f117,plain,(
% 0.19/0.51    ~r1_tarski(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)),sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))) | spl5_2),
% 0.19/0.51    inference(resolution,[],[f94,f43])).
% 0.19/0.51  fof(f43,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f18])).
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(flattening,[],[f17])).
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f13])).
% 0.19/0.51  fof(f13,axiom,(
% 0.19/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.19/0.51  fof(f94,plain,(
% 0.19/0.51    ~r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),k2_relat_1(sK3)) | spl5_2),
% 0.19/0.51    inference(avatar_component_clause,[],[f92])).
% 0.19/0.51  fof(f125,plain,(
% 0.19/0.51    spl5_3),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f124])).
% 0.19/0.51  fof(f124,plain,(
% 0.19/0.51    $false | spl5_3),
% 0.19/0.51    inference(resolution,[],[f120,f74])).
% 0.19/0.51  fof(f74,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f45,f72])).
% 0.19/0.51  fof(f72,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.19/0.51    inference(definition_unfolding,[],[f46,f71])).
% 0.19/0.51  fof(f71,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f47,f70])).
% 0.19/0.51  fof(f70,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f51,f69])).
% 0.19/0.51  fof(f69,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f53,f68])).
% 0.19/0.51  fof(f53,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f5])).
% 0.19/0.51  fof(f5,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.19/0.51  fof(f51,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.51  fof(f47,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.51  fof(f46,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f9])).
% 0.19/0.51  fof(f9,axiom,(
% 0.19/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.19/0.51  fof(f45,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.19/0.51  fof(f120,plain,(
% 0.19/0.51    ~r1_tarski(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)),sK2) | spl5_3),
% 0.19/0.51    inference(resolution,[],[f118,f39])).
% 0.19/0.51  fof(f39,plain,(
% 0.19/0.51    v1_relat_1(sK2)),
% 0.19/0.51    inference(cnf_transformation,[],[f29])).
% 0.19/0.51  fof(f118,plain,(
% 0.19/0.51    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)),X0)) ) | spl5_3),
% 0.19/0.51    inference(resolution,[],[f113,f50])).
% 0.19/0.51  fof(f50,plain,(
% 0.19/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f30])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.51    inference(nnf_transformation,[],[f10])).
% 0.19/0.51  fof(f10,axiom,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.51  fof(f113,plain,(
% 0.19/0.51    ( ! [X0] : (~m1_subset_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)),k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl5_3),
% 0.19/0.51    inference(resolution,[],[f100,f44])).
% 0.19/0.51  fof(f44,plain,(
% 0.19/0.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f19])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f12])).
% 0.19/0.51  fof(f12,axiom,(
% 0.19/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.51  fof(f100,plain,(
% 0.19/0.51    ~v1_relat_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))) | spl5_3),
% 0.19/0.51    inference(avatar_component_clause,[],[f98])).
% 0.19/0.51  fof(f116,plain,(
% 0.19/0.51    spl5_5),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f115])).
% 0.19/0.51  fof(f115,plain,(
% 0.19/0.51    $false | spl5_5),
% 0.19/0.51    inference(resolution,[],[f108,f74])).
% 0.19/0.51  fof(f108,plain,(
% 0.19/0.51    ~r1_tarski(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)),sK2) | spl5_5),
% 0.19/0.51    inference(avatar_component_clause,[],[f106])).
% 0.19/0.51  fof(f106,plain,(
% 0.19/0.51    spl5_5 <=> r1_tarski(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)),sK2)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.19/0.51  fof(f112,plain,(
% 0.19/0.51    spl5_4),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f110])).
% 0.19/0.51  fof(f110,plain,(
% 0.19/0.51    $false | spl5_4),
% 0.19/0.51    inference(resolution,[],[f104,f39])).
% 0.19/0.51  fof(f104,plain,(
% 0.19/0.51    ~v1_relat_1(sK2) | spl5_4),
% 0.19/0.51    inference(avatar_component_clause,[],[f102])).
% 0.19/0.51  % (31694)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.51  fof(f102,plain,(
% 0.19/0.51    spl5_4 <=> v1_relat_1(sK2)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.19/0.51  fof(f109,plain,(
% 0.19/0.51    ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_1),
% 0.19/0.51    inference(avatar_split_clause,[],[f96,f88,f106,f102,f98])).
% 0.19/0.51  fof(f88,plain,(
% 0.19/0.51    spl5_1 <=> r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),k2_relat_1(sK2))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.51  fof(f96,plain,(
% 0.19/0.51    ~r1_tarski(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)),sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))) | spl5_1),
% 0.19/0.51    inference(resolution,[],[f90,f43])).
% 0.19/0.51  fof(f90,plain,(
% 0.19/0.51    ~r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),k2_relat_1(sK2)) | spl5_1),
% 0.19/0.51    inference(avatar_component_clause,[],[f88])).
% 0.19/0.51  fof(f95,plain,(
% 0.19/0.51    ~spl5_1 | ~spl5_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f86,f92,f88])).
% 0.19/0.51  fof(f86,plain,(
% 0.19/0.51    ~r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),k2_relat_1(sK3)) | ~r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),k2_relat_1(sK2))),
% 0.19/0.51    inference(resolution,[],[f75,f73])).
% 0.19/0.51  fof(f73,plain,(
% 0.19/0.51    ~r1_tarski(k2_relat_1(k1_setfam_1(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),k1_setfam_1(k5_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(sK3))))),
% 0.19/0.51    inference(definition_unfolding,[],[f41,f72,f72])).
% 0.19/0.51  fof(f41,plain,(
% 0.19/0.51    ~r1_tarski(k2_relat_1(k3_xboole_0(sK2,sK3)),k3_xboole_0(k2_relat_1(sK2),k2_relat_1(sK3)))),
% 0.19/0.51    inference(cnf_transformation,[],[f29])).
% 0.19/0.51  fof(f75,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f52,f72])).
% 0.19/0.51  fof(f52,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f22])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.51    inference(flattening,[],[f21])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.51    inference(ennf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (31704)------------------------------
% 0.19/0.51  % (31704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (31704)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (31704)Memory used [KB]: 6268
% 0.19/0.51  % (31704)Time elapsed: 0.111 s
% 0.19/0.51  % (31704)------------------------------
% 0.19/0.51  % (31704)------------------------------
% 0.19/0.51  % (31686)Success in time 0.174 s
%------------------------------------------------------------------------------
