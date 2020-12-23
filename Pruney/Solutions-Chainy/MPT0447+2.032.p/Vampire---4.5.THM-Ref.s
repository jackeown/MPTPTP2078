%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:13 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 404 expanded)
%              Number of leaves         :   29 ( 133 expanded)
%              Depth                    :   16
%              Number of atoms          :  373 (1006 expanded)
%              Number of equality atoms :  115 ( 394 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f543,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f219,f250,f325,f452,f454,f471,f514,f542])).

fof(f542,plain,
    ( spl5_8
    | ~ spl5_47 ),
    inference(avatar_contradiction_clause,[],[f538])).

fof(f538,plain,
    ( $false
    | spl5_8
    | ~ spl5_47 ),
    inference(resolution,[],[f517,f218])).

fof(f218,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k3_relat_1(sK3))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl5_8
  <=> r1_tarski(k2_relat_1(sK2),k3_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f517,plain,
    ( r1_tarski(k2_relat_1(sK2),k3_relat_1(sK3))
    | ~ spl5_47 ),
    inference(resolution,[],[f506,f360])).

fof(f360,plain,(
    ! [X27] :
      ( ~ r1_tarski(X27,k2_relat_1(sK3))
      | r1_tarski(X27,k3_relat_1(sK3)) ) ),
    inference(resolution,[],[f340,f262])).

fof(f262,plain,(
    r1_tarski(k2_relat_1(sK3),k3_relat_1(sK3)) ),
    inference(superposition,[],[f103,f171])).

fof(f171,plain,(
    k3_relat_1(sK3) = k3_tarski(k6_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k2_relat_1(sK3))) ),
    inference(resolution,[],[f86,f45])).

fof(f45,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3))
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(X1))
          & r1_tarski(sK2,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(X1))
        & r1_tarski(sK2,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3))
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f48,f85])).

fof(f85,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f83])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f60,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f61,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f48,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

% (8244)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f21,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f103,plain,(
    ! [X6,X5] : r1_tarski(X5,k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X5))) ),
    inference(superposition,[],[f87,f88])).

fof(f88,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f52,f83,f83])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f87,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f51,f85])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f340,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0) ) ),
    inference(resolution,[],[f165,f91])).

fof(f91,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f165,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ sP0(X4,X5,X6,X6,X6,X6,X6,X6,X6)
      | ~ r1_tarski(X4,X7)
      | r1_tarski(X6,X7)
      | ~ r1_tarski(X6,X5) ) ),
    inference(resolution,[],[f162,f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
      | ~ r1_tarski(X3,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f58,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f84])).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f83])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

fof(f162,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1))
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(resolution,[],[f65,f99])).

fof(f99,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f29,f31,f30])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | r2_hidden(X10,X8) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ~ sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).

fof(f38,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X9,X8) )
          & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X9,X8) ) )
     => ( ( ~ sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f506,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_relat_1(sK3))
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f505])).

fof(f505,plain,
    ( spl5_47
  <=> r1_tarski(k2_relat_1(sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f514,plain,
    ( ~ spl5_13
    | ~ spl5_24
    | ~ spl5_41
    | spl5_47 ),
    inference(avatar_split_clause,[],[f513,f505,f449,f314,f241])).

fof(f241,plain,
    ( spl5_13
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f314,plain,
    ( spl5_24
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f449,plain,
    ( spl5_41
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f513,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | spl5_47 ),
    inference(resolution,[],[f507,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f507,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK3))
    | spl5_47 ),
    inference(avatar_component_clause,[],[f505])).

fof(f471,plain,
    ( spl5_7
    | ~ spl5_37 ),
    inference(avatar_contradiction_clause,[],[f468])).

fof(f468,plain,
    ( $false
    | spl5_7
    | ~ spl5_37 ),
    inference(resolution,[],[f456,f214])).

fof(f214,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl5_7
  <=> r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f456,plain,
    ( r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3))
    | ~ spl5_37 ),
    inference(resolution,[],[f430,f357])).

fof(f357,plain,(
    ! [X22] :
      ( ~ r1_tarski(X22,k1_relat_1(sK3))
      | r1_tarski(X22,k3_relat_1(sK3)) ) ),
    inference(resolution,[],[f340,f264])).

fof(f264,plain,(
    r1_tarski(k1_relat_1(sK3),k3_relat_1(sK3)) ),
    inference(superposition,[],[f87,f171])).

fof(f430,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f429])).

fof(f429,plain,
    ( spl5_37
  <=> r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f454,plain,(
    spl5_41 ),
    inference(avatar_contradiction_clause,[],[f453])).

fof(f453,plain,
    ( $false
    | spl5_41 ),
    inference(resolution,[],[f451,f46])).

fof(f46,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f451,plain,
    ( ~ r1_tarski(sK2,sK3)
    | spl5_41 ),
    inference(avatar_component_clause,[],[f449])).

fof(f452,plain,
    ( ~ spl5_13
    | ~ spl5_24
    | ~ spl5_41
    | spl5_37 ),
    inference(avatar_split_clause,[],[f447,f429,f449,f314,f241])).

fof(f447,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | spl5_37 ),
    inference(resolution,[],[f431,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f431,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | spl5_37 ),
    inference(avatar_component_clause,[],[f429])).

fof(f325,plain,(
    spl5_24 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | spl5_24 ),
    inference(resolution,[],[f316,f45])).

fof(f316,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_24 ),
    inference(avatar_component_clause,[],[f314])).

fof(f250,plain,(
    spl5_13 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | spl5_13 ),
    inference(resolution,[],[f243,f44])).

fof(f44,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f243,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f241])).

fof(f219,plain,
    ( ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f207,f216,f212])).

fof(f207,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k3_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3)) ),
    inference(resolution,[],[f173,f47])).

fof(f47,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f173,plain,(
    ! [X0] :
      ( r1_tarski(k3_relat_1(sK2),X0)
      | ~ r1_tarski(k2_relat_1(sK2),X0)
      | ~ r1_tarski(k1_relat_1(sK2),X0) ) ),
    inference(superposition,[],[f90,f170])).

fof(f170,plain,(
    k3_relat_1(sK2) = k3_tarski(k6_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(resolution,[],[f86,f44])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f85])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:35:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (8216)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (8222)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (8240)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (8231)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (8220)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (8221)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (8226)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (8226)Refutation not found, incomplete strategy% (8226)------------------------------
% 0.21/0.51  % (8226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8226)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (8226)Memory used [KB]: 10618
% 0.21/0.51  % (8226)Time elapsed: 0.096 s
% 0.21/0.51  % (8226)------------------------------
% 0.21/0.51  % (8226)------------------------------
% 0.21/0.51  % (8225)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (8238)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (8230)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (8228)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (8218)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (8227)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (8238)Refutation not found, incomplete strategy% (8238)------------------------------
% 0.21/0.53  % (8238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8219)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (8215)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (8229)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (8232)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (8223)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (8239)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (8238)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8238)Memory used [KB]: 1791
% 0.21/0.54  % (8238)Time elapsed: 0.124 s
% 0.21/0.54  % (8238)------------------------------
% 0.21/0.54  % (8238)------------------------------
% 0.21/0.54  % (8246)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (8235)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (8243)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (8239)Refutation not found, incomplete strategy% (8239)------------------------------
% 0.21/0.55  % (8239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (8234)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (8242)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (8245)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (8224)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (8233)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (8241)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.52/0.55  % (8239)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.55  
% 1.52/0.55  % (8239)Memory used [KB]: 10746
% 1.52/0.55  % (8239)Time elapsed: 0.141 s
% 1.52/0.55  % (8239)------------------------------
% 1.52/0.55  % (8239)------------------------------
% 1.52/0.55  % (8227)Refutation not found, incomplete strategy% (8227)------------------------------
% 1.52/0.55  % (8227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.55  % (8227)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.55  
% 1.52/0.55  % (8227)Memory used [KB]: 10618
% 1.52/0.55  % (8227)Time elapsed: 0.141 s
% 1.52/0.55  % (8227)------------------------------
% 1.52/0.55  % (8227)------------------------------
% 1.52/0.55  % (8218)Refutation not found, incomplete strategy% (8218)------------------------------
% 1.52/0.55  % (8218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.55  % (8218)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.55  
% 1.52/0.55  % (8218)Memory used [KB]: 10874
% 1.52/0.55  % (8218)Time elapsed: 0.132 s
% 1.52/0.55  % (8218)------------------------------
% 1.52/0.55  % (8218)------------------------------
% 1.52/0.56  % (8228)Refutation found. Thanks to Tanya!
% 1.52/0.56  % SZS status Theorem for theBenchmark
% 1.52/0.56  % SZS output start Proof for theBenchmark
% 1.52/0.56  fof(f543,plain,(
% 1.52/0.56    $false),
% 1.52/0.56    inference(avatar_sat_refutation,[],[f219,f250,f325,f452,f454,f471,f514,f542])).
% 1.52/0.56  fof(f542,plain,(
% 1.52/0.56    spl5_8 | ~spl5_47),
% 1.52/0.56    inference(avatar_contradiction_clause,[],[f538])).
% 1.52/0.56  fof(f538,plain,(
% 1.52/0.56    $false | (spl5_8 | ~spl5_47)),
% 1.52/0.56    inference(resolution,[],[f517,f218])).
% 1.52/0.56  fof(f218,plain,(
% 1.52/0.56    ~r1_tarski(k2_relat_1(sK2),k3_relat_1(sK3)) | spl5_8),
% 1.52/0.56    inference(avatar_component_clause,[],[f216])).
% 1.52/0.56  fof(f216,plain,(
% 1.52/0.56    spl5_8 <=> r1_tarski(k2_relat_1(sK2),k3_relat_1(sK3))),
% 1.52/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.52/0.56  fof(f517,plain,(
% 1.52/0.56    r1_tarski(k2_relat_1(sK2),k3_relat_1(sK3)) | ~spl5_47),
% 1.52/0.56    inference(resolution,[],[f506,f360])).
% 1.52/0.56  fof(f360,plain,(
% 1.52/0.56    ( ! [X27] : (~r1_tarski(X27,k2_relat_1(sK3)) | r1_tarski(X27,k3_relat_1(sK3))) )),
% 1.52/0.56    inference(resolution,[],[f340,f262])).
% 1.52/0.56  fof(f262,plain,(
% 1.52/0.56    r1_tarski(k2_relat_1(sK3),k3_relat_1(sK3))),
% 1.52/0.56    inference(superposition,[],[f103,f171])).
% 1.52/0.56  fof(f171,plain,(
% 1.52/0.56    k3_relat_1(sK3) = k3_tarski(k6_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k2_relat_1(sK3)))),
% 1.52/0.56    inference(resolution,[],[f86,f45])).
% 1.52/0.56  fof(f45,plain,(
% 1.52/0.56    v1_relat_1(sK3)),
% 1.52/0.56    inference(cnf_transformation,[],[f35])).
% 1.52/0.56  fof(f35,plain,(
% 1.52/0.56    (~r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 1.52/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f34,f33])).
% 1.52/0.56  fof(f33,plain,(
% 1.52/0.56    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK2),k3_relat_1(X1)) & r1_tarski(sK2,X1) & v1_relat_1(X1)) & v1_relat_1(sK2))),
% 1.52/0.56    introduced(choice_axiom,[])).
% 1.52/0.56  fof(f34,plain,(
% 1.52/0.56    ? [X1] : (~r1_tarski(k3_relat_1(sK2),k3_relat_1(X1)) & r1_tarski(sK2,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 1.52/0.56    introduced(choice_axiom,[])).
% 1.52/0.56  fof(f20,plain,(
% 1.52/0.56    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.52/0.56    inference(flattening,[],[f19])).
% 1.52/0.56  fof(f19,plain,(
% 1.52/0.56    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.52/0.56    inference(ennf_transformation,[],[f18])).
% 1.52/0.56  fof(f18,negated_conjecture,(
% 1.52/0.56    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.52/0.56    inference(negated_conjecture,[],[f17])).
% 1.52/0.56  fof(f17,conjecture,(
% 1.52/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 1.52/0.56  fof(f86,plain,(
% 1.52/0.56    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 1.52/0.56    inference(definition_unfolding,[],[f48,f85])).
% 1.52/0.56  fof(f85,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.52/0.56    inference(definition_unfolding,[],[f54,f83])).
% 1.52/0.56  fof(f83,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.52/0.56    inference(definition_unfolding,[],[f55,f82])).
% 1.52/0.56  fof(f82,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.52/0.56    inference(definition_unfolding,[],[f57,f81])).
% 1.52/0.56  fof(f81,plain,(
% 1.52/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.52/0.56    inference(definition_unfolding,[],[f60,f80])).
% 1.52/0.56  fof(f80,plain,(
% 1.52/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.52/0.56    inference(definition_unfolding,[],[f61,f79])).
% 1.52/0.56  fof(f79,plain,(
% 1.52/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.52/0.56    inference(definition_unfolding,[],[f62,f63])).
% 1.52/0.56  fof(f63,plain,(
% 1.52/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f10])).
% 1.52/0.56  fof(f10,axiom,(
% 1.52/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.52/0.56  fof(f62,plain,(
% 1.52/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f9])).
% 1.52/0.56  fof(f9,axiom,(
% 1.52/0.56    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.52/0.56  fof(f61,plain,(
% 1.52/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f8])).
% 1.52/0.56  fof(f8,axiom,(
% 1.52/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.52/0.56  fof(f60,plain,(
% 1.52/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f7])).
% 1.52/0.56  fof(f7,axiom,(
% 1.52/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.52/0.56  fof(f57,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f6])).
% 1.52/0.56  fof(f6,axiom,(
% 1.52/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.52/0.56  fof(f55,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f5])).
% 1.52/0.56  fof(f5,axiom,(
% 1.52/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.52/0.56  fof(f54,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.52/0.56    inference(cnf_transformation,[],[f11])).
% 1.52/0.56  fof(f11,axiom,(
% 1.52/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.52/0.56  fof(f48,plain,(
% 1.52/0.56    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f21])).
% 1.52/0.56  % (8244)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.52/0.56  fof(f21,plain,(
% 1.52/0.56    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.52/0.56    inference(ennf_transformation,[],[f15])).
% 1.52/0.56  fof(f15,axiom,(
% 1.52/0.56    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 1.52/0.56  fof(f103,plain,(
% 1.52/0.56    ( ! [X6,X5] : (r1_tarski(X5,k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X5)))) )),
% 1.52/0.56    inference(superposition,[],[f87,f88])).
% 1.52/0.56  fof(f88,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 1.52/0.56    inference(definition_unfolding,[],[f52,f83,f83])).
% 1.52/0.56  fof(f52,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f4])).
% 1.52/0.56  fof(f4,axiom,(
% 1.52/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.52/0.56  fof(f87,plain,(
% 1.52/0.56    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.52/0.56    inference(definition_unfolding,[],[f51,f85])).
% 1.52/0.56  fof(f51,plain,(
% 1.52/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.52/0.56    inference(cnf_transformation,[],[f2])).
% 1.52/0.56  fof(f2,axiom,(
% 1.52/0.56    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.52/0.56  fof(f340,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X2,X1) | ~r1_tarski(X2,X0)) )),
% 1.52/0.56    inference(resolution,[],[f165,f91])).
% 1.52/0.56  fof(f91,plain,(
% 1.52/0.56    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 1.52/0.56    inference(equality_resolution,[],[f76])).
% 1.52/0.56  fof(f76,plain,(
% 1.52/0.56    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X1) )),
% 1.52/0.56    inference(cnf_transformation,[],[f42])).
% 1.52/0.56  fof(f42,plain,(
% 1.52/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.52/0.56    inference(rectify,[],[f41])).
% 1.52/0.56  fof(f41,plain,(
% 1.52/0.56    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.52/0.56    inference(flattening,[],[f40])).
% 1.52/0.56  fof(f40,plain,(
% 1.52/0.56    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.52/0.56    inference(nnf_transformation,[],[f30])).
% 1.52/0.56  fof(f30,plain,(
% 1.52/0.56    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 1.52/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.52/0.56  fof(f165,plain,(
% 1.52/0.56    ( ! [X6,X4,X7,X5] : (~sP0(X4,X5,X6,X6,X6,X6,X6,X6,X6) | ~r1_tarski(X4,X7) | r1_tarski(X6,X7) | ~r1_tarski(X6,X5)) )),
% 1.52/0.56    inference(resolution,[],[f162,f100])).
% 1.52/0.56  fof(f100,plain,(
% 1.52/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) | ~r1_tarski(X3,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.52/0.56    inference(superposition,[],[f58,f89])).
% 1.52/0.56  fof(f89,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.52/0.56    inference(definition_unfolding,[],[f56,f84])).
% 1.52/0.56  fof(f84,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.52/0.56    inference(definition_unfolding,[],[f53,f83])).
% 1.52/0.56  fof(f53,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.52/0.56    inference(cnf_transformation,[],[f13])).
% 1.52/0.56  fof(f13,axiom,(
% 1.52/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.52/0.56  fof(f56,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f24])).
% 1.52/0.56  fof(f24,plain,(
% 1.52/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.52/0.56    inference(ennf_transformation,[],[f1])).
% 1.52/0.56  fof(f1,axiom,(
% 1.52/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.52/0.56  fof(f58,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f26])).
% 1.52/0.56  fof(f26,plain,(
% 1.52/0.56    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 1.52/0.56    inference(flattening,[],[f25])).
% 1.52/0.56  fof(f25,plain,(
% 1.52/0.56    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 1.52/0.56    inference(ennf_transformation,[],[f14])).
% 1.52/0.56  fof(f14,axiom,(
% 1.52/0.56    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).
% 1.52/0.56  fof(f162,plain,(
% 1.52/0.56    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1)) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 1.52/0.56    inference(resolution,[],[f65,f99])).
% 1.52/0.56  fof(f99,plain,(
% 1.52/0.56    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 1.52/0.56    inference(equality_resolution,[],[f77])).
% 1.52/0.56  fof(f77,plain,(
% 1.52/0.56    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 1.52/0.56    inference(cnf_transformation,[],[f43])).
% 1.52/0.56  fof(f43,plain,(
% 1.52/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 1.52/0.56    inference(nnf_transformation,[],[f32])).
% 1.52/0.56  fof(f32,plain,(
% 1.52/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 1.52/0.56    inference(definition_folding,[],[f29,f31,f30])).
% 1.52/0.56  fof(f31,plain,(
% 1.52/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.52/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.52/0.56  fof(f29,plain,(
% 1.52/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 1.52/0.56    inference(ennf_transformation,[],[f12])).
% 1.52/0.56  fof(f12,axiom,(
% 1.52/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).
% 1.52/0.56  fof(f65,plain,(
% 1.52/0.56    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X8)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f39])).
% 1.52/0.56  fof(f39,plain,(
% 1.52/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.52/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).
% 1.52/0.56  fof(f38,plain,(
% 1.52/0.56    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 1.52/0.56    introduced(choice_axiom,[])).
% 1.52/0.56  fof(f37,plain,(
% 1.52/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.52/0.56    inference(rectify,[],[f36])).
% 1.52/0.56  fof(f36,plain,(
% 1.52/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.52/0.56    inference(nnf_transformation,[],[f31])).
% 1.52/0.56  fof(f506,plain,(
% 1.52/0.56    r1_tarski(k2_relat_1(sK2),k2_relat_1(sK3)) | ~spl5_47),
% 1.52/0.56    inference(avatar_component_clause,[],[f505])).
% 1.52/0.56  fof(f505,plain,(
% 1.52/0.56    spl5_47 <=> r1_tarski(k2_relat_1(sK2),k2_relat_1(sK3))),
% 1.52/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 1.52/0.56  fof(f514,plain,(
% 1.52/0.56    ~spl5_13 | ~spl5_24 | ~spl5_41 | spl5_47),
% 1.52/0.56    inference(avatar_split_clause,[],[f513,f505,f449,f314,f241])).
% 1.52/0.56  fof(f241,plain,(
% 1.52/0.56    spl5_13 <=> v1_relat_1(sK2)),
% 1.52/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.52/0.56  fof(f314,plain,(
% 1.52/0.56    spl5_24 <=> v1_relat_1(sK3)),
% 1.52/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.52/0.56  fof(f449,plain,(
% 1.52/0.56    spl5_41 <=> r1_tarski(sK2,sK3)),
% 1.52/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 1.52/0.56  fof(f513,plain,(
% 1.52/0.56    ~r1_tarski(sK2,sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | spl5_47),
% 1.52/0.56    inference(resolution,[],[f507,f50])).
% 1.52/0.56  fof(f50,plain,(
% 1.52/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f23])).
% 1.52/0.56  fof(f23,plain,(
% 1.52/0.56    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.52/0.56    inference(flattening,[],[f22])).
% 1.52/0.56  fof(f22,plain,(
% 1.52/0.56    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.52/0.56    inference(ennf_transformation,[],[f16])).
% 1.52/0.56  fof(f16,axiom,(
% 1.52/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 1.52/0.56  fof(f507,plain,(
% 1.52/0.56    ~r1_tarski(k2_relat_1(sK2),k2_relat_1(sK3)) | spl5_47),
% 1.52/0.56    inference(avatar_component_clause,[],[f505])).
% 1.52/0.56  fof(f471,plain,(
% 1.52/0.56    spl5_7 | ~spl5_37),
% 1.52/0.56    inference(avatar_contradiction_clause,[],[f468])).
% 1.52/0.56  fof(f468,plain,(
% 1.52/0.56    $false | (spl5_7 | ~spl5_37)),
% 1.52/0.56    inference(resolution,[],[f456,f214])).
% 1.52/0.56  fof(f214,plain,(
% 1.52/0.56    ~r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3)) | spl5_7),
% 1.52/0.56    inference(avatar_component_clause,[],[f212])).
% 1.52/0.56  fof(f212,plain,(
% 1.52/0.56    spl5_7 <=> r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3))),
% 1.52/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.52/0.56  fof(f456,plain,(
% 1.52/0.56    r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3)) | ~spl5_37),
% 1.52/0.56    inference(resolution,[],[f430,f357])).
% 1.52/0.56  fof(f357,plain,(
% 1.52/0.56    ( ! [X22] : (~r1_tarski(X22,k1_relat_1(sK3)) | r1_tarski(X22,k3_relat_1(sK3))) )),
% 1.52/0.56    inference(resolution,[],[f340,f264])).
% 1.52/0.56  fof(f264,plain,(
% 1.52/0.56    r1_tarski(k1_relat_1(sK3),k3_relat_1(sK3))),
% 1.52/0.56    inference(superposition,[],[f87,f171])).
% 1.52/0.56  fof(f430,plain,(
% 1.52/0.56    r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~spl5_37),
% 1.52/0.56    inference(avatar_component_clause,[],[f429])).
% 1.52/0.56  fof(f429,plain,(
% 1.52/0.56    spl5_37 <=> r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))),
% 1.52/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 1.52/0.56  fof(f454,plain,(
% 1.52/0.56    spl5_41),
% 1.52/0.56    inference(avatar_contradiction_clause,[],[f453])).
% 1.52/0.56  fof(f453,plain,(
% 1.52/0.56    $false | spl5_41),
% 1.52/0.56    inference(resolution,[],[f451,f46])).
% 1.52/0.56  fof(f46,plain,(
% 1.52/0.56    r1_tarski(sK2,sK3)),
% 1.52/0.56    inference(cnf_transformation,[],[f35])).
% 1.52/0.56  fof(f451,plain,(
% 1.52/0.56    ~r1_tarski(sK2,sK3) | spl5_41),
% 1.52/0.56    inference(avatar_component_clause,[],[f449])).
% 1.52/0.56  fof(f452,plain,(
% 1.52/0.56    ~spl5_13 | ~spl5_24 | ~spl5_41 | spl5_37),
% 1.52/0.56    inference(avatar_split_clause,[],[f447,f429,f449,f314,f241])).
% 1.52/0.56  fof(f447,plain,(
% 1.52/0.56    ~r1_tarski(sK2,sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | spl5_37),
% 1.52/0.56    inference(resolution,[],[f431,f49])).
% 1.52/0.56  fof(f49,plain,(
% 1.52/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f23])).
% 1.52/0.56  fof(f431,plain,(
% 1.52/0.56    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | spl5_37),
% 1.52/0.56    inference(avatar_component_clause,[],[f429])).
% 1.52/0.56  fof(f325,plain,(
% 1.52/0.56    spl5_24),
% 1.52/0.56    inference(avatar_contradiction_clause,[],[f324])).
% 1.52/0.56  fof(f324,plain,(
% 1.52/0.56    $false | spl5_24),
% 1.52/0.56    inference(resolution,[],[f316,f45])).
% 1.52/0.56  fof(f316,plain,(
% 1.52/0.56    ~v1_relat_1(sK3) | spl5_24),
% 1.52/0.56    inference(avatar_component_clause,[],[f314])).
% 1.52/0.56  fof(f250,plain,(
% 1.52/0.56    spl5_13),
% 1.52/0.56    inference(avatar_contradiction_clause,[],[f249])).
% 1.52/0.56  fof(f249,plain,(
% 1.52/0.56    $false | spl5_13),
% 1.52/0.56    inference(resolution,[],[f243,f44])).
% 1.52/0.56  fof(f44,plain,(
% 1.52/0.56    v1_relat_1(sK2)),
% 1.52/0.56    inference(cnf_transformation,[],[f35])).
% 1.52/0.56  fof(f243,plain,(
% 1.52/0.56    ~v1_relat_1(sK2) | spl5_13),
% 1.52/0.56    inference(avatar_component_clause,[],[f241])).
% 1.52/0.56  fof(f219,plain,(
% 1.52/0.56    ~spl5_7 | ~spl5_8),
% 1.52/0.56    inference(avatar_split_clause,[],[f207,f216,f212])).
% 1.52/0.56  fof(f207,plain,(
% 1.52/0.56    ~r1_tarski(k2_relat_1(sK2),k3_relat_1(sK3)) | ~r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3))),
% 1.52/0.56    inference(resolution,[],[f173,f47])).
% 1.52/0.56  fof(f47,plain,(
% 1.52/0.56    ~r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3))),
% 1.52/0.56    inference(cnf_transformation,[],[f35])).
% 1.52/0.56  fof(f173,plain,(
% 1.52/0.56    ( ! [X0] : (r1_tarski(k3_relat_1(sK2),X0) | ~r1_tarski(k2_relat_1(sK2),X0) | ~r1_tarski(k1_relat_1(sK2),X0)) )),
% 1.52/0.56    inference(superposition,[],[f90,f170])).
% 1.52/0.56  fof(f170,plain,(
% 1.52/0.56    k3_relat_1(sK2) = k3_tarski(k6_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2)))),
% 1.52/0.56    inference(resolution,[],[f86,f44])).
% 1.52/0.56  fof(f90,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.52/0.56    inference(definition_unfolding,[],[f59,f85])).
% 1.52/0.56  fof(f59,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f28])).
% 1.52/0.56  fof(f28,plain,(
% 1.52/0.56    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.52/0.56    inference(flattening,[],[f27])).
% 1.52/0.56  fof(f27,plain,(
% 1.52/0.56    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.52/0.56    inference(ennf_transformation,[],[f3])).
% 1.52/0.56  fof(f3,axiom,(
% 1.52/0.56    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.52/0.56  % SZS output end Proof for theBenchmark
% 1.52/0.56  % (8228)------------------------------
% 1.52/0.56  % (8228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (8228)Termination reason: Refutation
% 1.52/0.56  
% 1.52/0.56  % (8228)Memory used [KB]: 6652
% 1.52/0.56  % (8228)Time elapsed: 0.138 s
% 1.52/0.56  % (8228)------------------------------
% 1.52/0.56  % (8228)------------------------------
% 1.52/0.56  % (8212)Success in time 0.199 s
%------------------------------------------------------------------------------
