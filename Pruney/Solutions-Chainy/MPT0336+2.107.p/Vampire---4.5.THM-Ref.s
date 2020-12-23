%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:38 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 150 expanded)
%              Number of leaves         :   20 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  204 ( 355 expanded)
%              Number of equality atoms :   22 (  58 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1388,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1271,f1328,f1349,f1387])).

fof(f1387,plain,
    ( ~ spl5_28
    | ~ spl5_38 ),
    inference(avatar_contradiction_clause,[],[f1383])).

fof(f1383,plain,
    ( $false
    | ~ spl5_28
    | ~ spl5_38 ),
    inference(resolution,[],[f1367,f1326])).

fof(f1326,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f1325])).

fof(f1325,plain,
    ( spl5_38
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f1367,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ spl5_28 ),
    inference(resolution,[],[f1270,f106])).

fof(f106,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f43,f32])).

fof(f32,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f1270,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f1268])).

fof(f1268,plain,
    ( spl5_28
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f1349,plain,(
    spl5_38 ),
    inference(avatar_contradiction_clause,[],[f1345])).

fof(f1345,plain,
    ( $false
    | spl5_38 ),
    inference(resolution,[],[f1344,f33])).

fof(f33,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f1344,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl5_38 ),
    inference(resolution,[],[f1327,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1327,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl5_38 ),
    inference(avatar_component_clause,[],[f1325])).

fof(f1328,plain,
    ( ~ spl5_38
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f175,f1264,f1325])).

fof(f1264,plain,
    ( spl5_27
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f175,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f65,f67])).

fof(f67,plain,(
    ~ r1_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2))) ),
    inference(resolution,[],[f59,f44])).

fof(f59,plain,(
    ~ r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1) ),
    inference(definition_unfolding,[],[f34,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f34,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(definition_unfolding,[],[f50,f57])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f1271,plain,
    ( spl5_27
    | spl5_28 ),
    inference(avatar_split_clause,[],[f1262,f1268,f1264])).

fof(f1262,plain,
    ( r2_hidden(sK3,sK1)
    | r1_xboole_0(sK1,sK0) ),
    inference(condensation,[],[f1260])).

fof(f1260,plain,(
    ! [X6] :
      ( r1_xboole_0(sK1,sK0)
      | r2_hidden(sK3,sK1)
      | r2_hidden(X6,sK1) ) ),
    inference(resolution,[],[f1232,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f36,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f48,f58])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f56])).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1232,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK1)
      | r1_xboole_0(X2,sK0)
      | r2_hidden(sK3,X2) ) ),
    inference(resolution,[],[f1070,f123])).

fof(f123,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X2,k2_enumset1(X3,X3,X3,X3))
      | r2_hidden(X3,X2) ) ),
    inference(superposition,[],[f37,f61])).

fof(f37,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f1070,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(X2,k2_enumset1(sK3,sK3,sK3,sK3))
      | ~ r1_tarski(X2,sK1)
      | r1_xboole_0(X2,sK0) ) ),
    inference(resolution,[],[f393,f44])).

fof(f393,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),X0)
      | r1_xboole_0(X0,sK0)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f147,f151])).

fof(f151,plain,(
    ! [X12,X13,X11] :
      ( ~ r1_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X12)),X11)
      | r1_xboole_0(X11,X13)
      | ~ r1_tarski(X11,X12) ) ),
    inference(resolution,[],[f66,f44])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f147,plain,(
    ! [X13] :
      ( r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X13)
      | ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),X13) ) ),
    inference(resolution,[],[f77,f60])).

fof(f60,plain,(
    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f31,f40,f58])).

fof(f31,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r1_xboole_0(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f54,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (18519)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.46  % (18511)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (18509)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (18513)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (18523)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (18524)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (18515)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (18514)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (18516)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (18518)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (18512)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (18522)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (18510)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (18521)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (18526)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (18525)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.27/0.51  % (18520)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.27/0.52  % (18513)Refutation found. Thanks to Tanya!
% 1.27/0.52  % SZS status Theorem for theBenchmark
% 1.27/0.52  % SZS output start Proof for theBenchmark
% 1.27/0.52  fof(f1388,plain,(
% 1.27/0.52    $false),
% 1.27/0.52    inference(avatar_sat_refutation,[],[f1271,f1328,f1349,f1387])).
% 1.27/0.52  fof(f1387,plain,(
% 1.27/0.52    ~spl5_28 | ~spl5_38),
% 1.27/0.52    inference(avatar_contradiction_clause,[],[f1383])).
% 1.27/0.52  fof(f1383,plain,(
% 1.27/0.52    $false | (~spl5_28 | ~spl5_38)),
% 1.27/0.52    inference(resolution,[],[f1367,f1326])).
% 1.27/0.52  fof(f1326,plain,(
% 1.27/0.52    r1_xboole_0(sK1,sK2) | ~spl5_38),
% 1.27/0.52    inference(avatar_component_clause,[],[f1325])).
% 1.27/0.52  fof(f1325,plain,(
% 1.27/0.52    spl5_38 <=> r1_xboole_0(sK1,sK2)),
% 1.27/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 1.27/0.52  fof(f1367,plain,(
% 1.27/0.52    ~r1_xboole_0(sK1,sK2) | ~spl5_28),
% 1.27/0.52    inference(resolution,[],[f1270,f106])).
% 1.27/0.52  fof(f106,plain,(
% 1.27/0.52    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(X0,sK2)) )),
% 1.27/0.52    inference(resolution,[],[f43,f32])).
% 1.27/0.52  fof(f32,plain,(
% 1.27/0.52    r2_hidden(sK3,sK2)),
% 1.27/0.52    inference(cnf_transformation,[],[f26])).
% 1.27/0.52  fof(f26,plain,(
% 1.27/0.52    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.27/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f25])).
% 1.27/0.52  fof(f25,plain,(
% 1.27/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 1.27/0.52    introduced(choice_axiom,[])).
% 1.27/0.52  fof(f19,plain,(
% 1.27/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.27/0.52    inference(flattening,[],[f18])).
% 1.27/0.52  fof(f18,plain,(
% 1.27/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.27/0.52    inference(ennf_transformation,[],[f16])).
% 1.27/0.52  fof(f16,negated_conjecture,(
% 1.27/0.52    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.27/0.52    inference(negated_conjecture,[],[f15])).
% 1.27/0.52  fof(f15,conjecture,(
% 1.27/0.52    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.27/0.52  fof(f43,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f28])).
% 1.27/0.52  fof(f28,plain,(
% 1.27/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.27/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f27])).
% 1.27/0.52  fof(f27,plain,(
% 1.27/0.52    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.27/0.52    introduced(choice_axiom,[])).
% 1.27/0.52  fof(f20,plain,(
% 1.27/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.27/0.52    inference(ennf_transformation,[],[f17])).
% 1.27/0.52  fof(f17,plain,(
% 1.27/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.27/0.52    inference(rectify,[],[f2])).
% 1.27/0.52  fof(f2,axiom,(
% 1.27/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.27/0.52  fof(f1270,plain,(
% 1.27/0.52    r2_hidden(sK3,sK1) | ~spl5_28),
% 1.27/0.52    inference(avatar_component_clause,[],[f1268])).
% 1.27/0.52  fof(f1268,plain,(
% 1.27/0.52    spl5_28 <=> r2_hidden(sK3,sK1)),
% 1.27/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 1.27/0.52  fof(f1349,plain,(
% 1.27/0.52    spl5_38),
% 1.27/0.52    inference(avatar_contradiction_clause,[],[f1345])).
% 1.27/0.52  fof(f1345,plain,(
% 1.27/0.52    $false | spl5_38),
% 1.27/0.52    inference(resolution,[],[f1344,f33])).
% 1.27/0.52  fof(f33,plain,(
% 1.27/0.52    r1_xboole_0(sK2,sK1)),
% 1.27/0.52    inference(cnf_transformation,[],[f26])).
% 1.27/0.52  fof(f1344,plain,(
% 1.27/0.52    ~r1_xboole_0(sK2,sK1) | spl5_38),
% 1.27/0.52    inference(resolution,[],[f1327,f44])).
% 1.27/0.52  fof(f44,plain,(
% 1.27/0.52    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f21])).
% 1.27/0.52  fof(f21,plain,(
% 1.27/0.52    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.27/0.52    inference(ennf_transformation,[],[f1])).
% 1.27/0.52  fof(f1,axiom,(
% 1.27/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.27/0.52  fof(f1327,plain,(
% 1.27/0.52    ~r1_xboole_0(sK1,sK2) | spl5_38),
% 1.27/0.52    inference(avatar_component_clause,[],[f1325])).
% 1.27/0.52  fof(f1328,plain,(
% 1.27/0.52    ~spl5_38 | ~spl5_27),
% 1.27/0.52    inference(avatar_split_clause,[],[f175,f1264,f1325])).
% 1.27/0.52  fof(f1264,plain,(
% 1.27/0.52    spl5_27 <=> r1_xboole_0(sK1,sK0)),
% 1.27/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 1.27/0.52  fof(f175,plain,(
% 1.27/0.52    ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK1,sK2)),
% 1.27/0.52    inference(resolution,[],[f65,f67])).
% 1.27/0.52  fof(f67,plain,(
% 1.27/0.52    ~r1_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)))),
% 1.27/0.52    inference(resolution,[],[f59,f44])).
% 1.27/0.52  fof(f59,plain,(
% 1.27/0.52    ~r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1)),
% 1.27/0.52    inference(definition_unfolding,[],[f34,f57])).
% 1.27/0.52  fof(f57,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.27/0.52    inference(definition_unfolding,[],[f38,f56])).
% 1.27/0.52  fof(f56,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.27/0.52    inference(definition_unfolding,[],[f39,f49])).
% 1.27/0.52  fof(f49,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f12])).
% 1.27/0.52  fof(f12,axiom,(
% 1.27/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.27/0.52  fof(f39,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f11])).
% 1.27/0.52  fof(f11,axiom,(
% 1.27/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.27/0.52  fof(f38,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f13])).
% 1.27/0.52  fof(f13,axiom,(
% 1.27/0.52    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.27/0.52  fof(f34,plain,(
% 1.27/0.52    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.27/0.52    inference(cnf_transformation,[],[f26])).
% 1.27/0.52  fof(f65,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 1.27/0.52    inference(definition_unfolding,[],[f50,f57])).
% 1.27/0.52  fof(f50,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.27/0.52    inference(cnf_transformation,[],[f22])).
% 1.27/0.52  fof(f22,plain,(
% 1.27/0.52    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.27/0.52    inference(ennf_transformation,[],[f6])).
% 1.27/0.52  fof(f6,axiom,(
% 1.27/0.52    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.27/0.52  fof(f1271,plain,(
% 1.27/0.52    spl5_27 | spl5_28),
% 1.27/0.52    inference(avatar_split_clause,[],[f1262,f1268,f1264])).
% 1.27/0.52  fof(f1262,plain,(
% 1.27/0.52    r2_hidden(sK3,sK1) | r1_xboole_0(sK1,sK0)),
% 1.27/0.52    inference(condensation,[],[f1260])).
% 1.27/0.52  fof(f1260,plain,(
% 1.27/0.52    ( ! [X6] : (r1_xboole_0(sK1,sK0) | r2_hidden(sK3,sK1) | r2_hidden(X6,sK1)) )),
% 1.27/0.52    inference(resolution,[],[f1232,f122])).
% 1.27/0.52  fof(f122,plain,(
% 1.27/0.52    ( ! [X0,X1] : (r1_tarski(X0,X0) | r2_hidden(X1,X0)) )),
% 1.27/0.52    inference(superposition,[],[f36,f61])).
% 1.27/0.52  fof(f61,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.27/0.52    inference(definition_unfolding,[],[f48,f58])).
% 1.27/0.52  fof(f58,plain,(
% 1.27/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.27/0.52    inference(definition_unfolding,[],[f35,f56])).
% 1.27/0.52  fof(f35,plain,(
% 1.27/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f10])).
% 1.27/0.52  fof(f10,axiom,(
% 1.27/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.27/0.52  fof(f48,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f30])).
% 1.27/0.52  fof(f30,plain,(
% 1.27/0.52    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.27/0.52    inference(nnf_transformation,[],[f14])).
% 1.27/0.52  fof(f14,axiom,(
% 1.27/0.52    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.27/0.52  fof(f36,plain,(
% 1.27/0.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f4])).
% 1.27/0.52  fof(f4,axiom,(
% 1.27/0.52    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.27/0.52  fof(f1232,plain,(
% 1.27/0.52    ( ! [X2] : (~r1_tarski(X2,sK1) | r1_xboole_0(X2,sK0) | r2_hidden(sK3,X2)) )),
% 1.27/0.52    inference(resolution,[],[f1070,f123])).
% 1.27/0.52  fof(f123,plain,(
% 1.27/0.52    ( ! [X2,X3] : (r1_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)) | r2_hidden(X3,X2)) )),
% 1.27/0.52    inference(superposition,[],[f37,f61])).
% 1.27/0.52  fof(f37,plain,(
% 1.27/0.52    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f8])).
% 1.27/0.52  fof(f8,axiom,(
% 1.27/0.52    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.27/0.52  fof(f1070,plain,(
% 1.27/0.52    ( ! [X2] : (~r1_xboole_0(X2,k2_enumset1(sK3,sK3,sK3,sK3)) | ~r1_tarski(X2,sK1) | r1_xboole_0(X2,sK0)) )),
% 1.27/0.52    inference(resolution,[],[f393,f44])).
% 1.27/0.52  fof(f393,plain,(
% 1.27/0.52    ( ! [X0] : (~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),X0) | r1_xboole_0(X0,sK0) | ~r1_tarski(X0,sK1)) )),
% 1.27/0.52    inference(resolution,[],[f147,f151])).
% 1.27/0.52  fof(f151,plain,(
% 1.27/0.52    ( ! [X12,X13,X11] : (~r1_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X12)),X11) | r1_xboole_0(X11,X13) | ~r1_tarski(X11,X12)) )),
% 1.27/0.52    inference(resolution,[],[f66,f44])).
% 1.27/0.52  fof(f66,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) )),
% 1.27/0.52    inference(definition_unfolding,[],[f55,f40])).
% 1.27/0.52  fof(f40,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f5])).
% 1.27/0.52  fof(f5,axiom,(
% 1.27/0.52    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.27/0.52  fof(f55,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f24])).
% 1.27/0.52  fof(f24,plain,(
% 1.27/0.52    ! [X0,X1,X2] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1))),
% 1.27/0.52    inference(ennf_transformation,[],[f7])).
% 1.27/0.52  fof(f7,axiom,(
% 1.27/0.52    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).
% 1.27/0.52  fof(f147,plain,(
% 1.27/0.52    ( ! [X13] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X13) | ~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),X13)) )),
% 1.27/0.52    inference(resolution,[],[f77,f60])).
% 1.27/0.52  fof(f60,plain,(
% 1.27/0.52    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.27/0.52    inference(definition_unfolding,[],[f31,f40,f58])).
% 1.27/0.52  fof(f31,plain,(
% 1.27/0.52    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.27/0.52    inference(cnf_transformation,[],[f26])).
% 1.27/0.52  fof(f77,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r1_xboole_0(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 1.27/0.52    inference(superposition,[],[f54,f45])).
% 1.27/0.52  fof(f45,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f29])).
% 1.27/0.52  fof(f29,plain,(
% 1.27/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.27/0.52    inference(nnf_transformation,[],[f9])).
% 1.27/0.52  fof(f9,axiom,(
% 1.27/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.27/0.52  fof(f54,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f23])).
% 1.27/0.52  fof(f23,plain,(
% 1.27/0.52    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.27/0.52    inference(ennf_transformation,[],[f3])).
% 1.27/0.52  fof(f3,axiom,(
% 1.27/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.27/0.52  % SZS output end Proof for theBenchmark
% 1.27/0.52  % (18513)------------------------------
% 1.27/0.52  % (18513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (18513)Termination reason: Refutation
% 1.27/0.52  
% 1.27/0.52  % (18513)Memory used [KB]: 6780
% 1.27/0.52  % (18513)Time elapsed: 0.110 s
% 1.27/0.52  % (18513)------------------------------
% 1.27/0.52  % (18513)------------------------------
% 1.27/0.52  % (18508)Success in time 0.163 s
%------------------------------------------------------------------------------
