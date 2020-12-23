%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 286 expanded)
%              Number of leaves         :   28 ( 103 expanded)
%              Depth                    :   14
%              Number of atoms          :  313 ( 783 expanded)
%              Number of equality atoms :   17 (  99 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f763,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f83,f324,f345,f572,f588,f595,f606,f657,f752,f756,f762])).

fof(f762,plain,
    ( ~ spl3_1
    | spl3_46 ),
    inference(avatar_contradiction_clause,[],[f761])).

fof(f761,plain,
    ( $false
    | ~ spl3_1
    | spl3_46 ),
    inference(resolution,[],[f757,f76])).

fof(f76,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f757,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl3_46 ),
    inference(resolution,[],[f751,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f751,plain,
    ( ~ r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | spl3_46 ),
    inference(avatar_component_clause,[],[f749])).

fof(f749,plain,
    ( spl3_46
  <=> r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f756,plain,
    ( ~ spl3_7
    | ~ spl3_9
    | ~ spl3_28
    | spl3_45 ),
    inference(avatar_split_clause,[],[f753,f745,f592,f331,f313])).

fof(f313,plain,
    ( spl3_7
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f331,plain,
    ( spl3_9
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f592,plain,
    ( spl3_28
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f745,plain,
    ( spl3_45
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f753,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | spl3_45 ),
    inference(resolution,[],[f747,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f747,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_45 ),
    inference(avatar_component_clause,[],[f745])).

fof(f752,plain,
    ( ~ spl3_45
    | ~ spl3_46
    | spl3_30 ),
    inference(avatar_split_clause,[],[f740,f603,f749,f745])).

fof(f603,plain,
    ( spl3_30
  <=> r1_tarski(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f740,plain,
    ( ~ r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ r1_tarski(sK0,sK1)
    | spl3_30 ),
    inference(resolution,[],[f605,f60])).

fof(f60,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f605,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1)
    | spl3_30 ),
    inference(avatar_component_clause,[],[f603])).

fof(f657,plain,(
    spl3_29 ),
    inference(avatar_contradiction_clause,[],[f656])).

fof(f656,plain,
    ( $false
    | spl3_29 ),
    inference(resolution,[],[f655,f40])).

fof(f40,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
            | ~ r2_hidden(sK0,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK0),X1)
            | r2_hidden(sK0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
          | ~ r2_hidden(sK0,X1) )
        & ( r1_ordinal1(k1_ordinal1(sK0),X1)
          | r2_hidden(sK0,X1) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
        | ~ r2_hidden(sK0,sK1) )
      & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
        | r2_hidden(sK0,sK1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f655,plain,
    ( ~ v3_ordinal1(sK0)
    | spl3_29 ),
    inference(resolution,[],[f601,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f47,f67])).

fof(f67,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f46,f66])).

fof(f46,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f47,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f601,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))
    | spl3_29 ),
    inference(avatar_component_clause,[],[f599])).

fof(f599,plain,
    ( spl3_29
  <=> v3_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f606,plain,
    ( ~ spl3_29
    | ~ spl3_9
    | ~ spl3_30
    | spl3_2 ),
    inference(avatar_split_clause,[],[f596,f79,f603,f331,f599])).

fof(f79,plain,
    ( spl3_2
  <=> r1_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f596,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))
    | spl3_2 ),
    inference(resolution,[],[f81,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f595,plain,
    ( ~ spl3_7
    | ~ spl3_9
    | spl3_28
    | spl3_27 ),
    inference(avatar_split_clause,[],[f590,f585,f592,f331,f313])).

fof(f585,plain,
    ( spl3_27
  <=> r1_ordinal1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f590,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | spl3_27 ),
    inference(resolution,[],[f587,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f587,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | spl3_27 ),
    inference(avatar_component_clause,[],[f585])).

fof(f588,plain,
    ( ~ spl3_9
    | ~ spl3_7
    | ~ spl3_27
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f581,f75,f585,f313,f331])).

fof(f581,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f580,f50])).

fof(f580,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f76,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f572,plain,
    ( ~ spl3_7
    | spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f569,f79,f75,f313])).

fof(f569,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f442,f80])).

fof(f80,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f442,plain,(
    ! [X1] :
      ( ~ r1_ordinal1(k2_xboole_0(X1,k4_enumset1(X1,X1,X1,X1,X1,X1)),sK1)
      | r2_hidden(X1,sK1)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f369,f41])).

fof(f41,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f369,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)),X1)
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f106,f71])).

fof(f106,plain,(
    ! [X2,X3] :
      ( ~ v3_ordinal1(k2_xboole_0(X2,k4_enumset1(X2,X2,X2,X2,X2,X2)))
      | ~ r1_ordinal1(k2_xboole_0(X2,k4_enumset1(X2,X2,X2,X2,X2,X2)),X3)
      | ~ v3_ordinal1(X3)
      | r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f86,f50])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)),X1)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f70,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f70,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f44,f67])).

fof(f44,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f345,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | spl3_9 ),
    inference(resolution,[],[f333,f41])).

fof(f333,plain,
    ( ~ v3_ordinal1(sK1)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f331])).

fof(f324,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f315,f40])).

fof(f315,plain,
    ( ~ v3_ordinal1(sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f313])).

fof(f83,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f69,f79,f75])).

fof(f69,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f42,f67])).

% (22969)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f42,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f68,f79,f75])).

fof(f68,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f43,f67])).

fof(f43,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:12:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.47  % (22971)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (22987)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (22971)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f763,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f82,f83,f324,f345,f572,f588,f595,f606,f657,f752,f756,f762])).
% 0.21/0.51  fof(f762,plain,(
% 0.21/0.51    ~spl3_1 | spl3_46),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f761])).
% 0.21/0.51  fof(f761,plain,(
% 0.21/0.51    $false | (~spl3_1 | spl3_46)),
% 0.21/0.51    inference(resolution,[],[f757,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    r2_hidden(sK0,sK1) | ~spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    spl3_1 <=> r2_hidden(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f757,plain,(
% 0.21/0.51    ~r2_hidden(sK0,sK1) | spl3_46),
% 0.21/0.51    inference(resolution,[],[f751,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f56,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f45,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f48,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f58,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f61,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.51  fof(f751,plain,(
% 0.21/0.51    ~r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1) | spl3_46),
% 0.21/0.51    inference(avatar_component_clause,[],[f749])).
% 0.21/0.51  fof(f749,plain,(
% 0.21/0.51    spl3_46 <=> r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.21/0.51  fof(f756,plain,(
% 0.21/0.51    ~spl3_7 | ~spl3_9 | ~spl3_28 | spl3_45),
% 0.21/0.51    inference(avatar_split_clause,[],[f753,f745,f592,f331,f313])).
% 0.21/0.51  fof(f313,plain,(
% 0.21/0.51    spl3_7 <=> v3_ordinal1(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.51  fof(f331,plain,(
% 0.21/0.51    spl3_9 <=> v3_ordinal1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.51  fof(f592,plain,(
% 0.21/0.51    spl3_28 <=> r1_ordinal1(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.51  fof(f745,plain,(
% 0.21/0.51    spl3_45 <=> r1_tarski(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.21/0.51  fof(f753,plain,(
% 0.21/0.51    ~r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | spl3_45),
% 0.21/0.51    inference(resolution,[],[f747,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.51  fof(f747,plain,(
% 0.21/0.51    ~r1_tarski(sK0,sK1) | spl3_45),
% 0.21/0.51    inference(avatar_component_clause,[],[f745])).
% 0.21/0.51  fof(f752,plain,(
% 0.21/0.51    ~spl3_45 | ~spl3_46 | spl3_30),
% 0.21/0.51    inference(avatar_split_clause,[],[f740,f603,f749,f745])).
% 0.21/0.51  fof(f603,plain,(
% 0.21/0.51    spl3_30 <=> r1_tarski(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.51  fof(f740,plain,(
% 0.21/0.51    ~r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1) | ~r1_tarski(sK0,sK1) | spl3_30),
% 0.21/0.51    inference(resolution,[],[f605,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.51  fof(f605,plain,(
% 0.21/0.51    ~r1_tarski(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1) | spl3_30),
% 0.21/0.51    inference(avatar_component_clause,[],[f603])).
% 0.21/0.51  fof(f657,plain,(
% 0.21/0.51    spl3_29),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f656])).
% 0.21/0.51  fof(f656,plain,(
% 0.21/0.51    $false | spl3_29),
% 0.21/0.51    inference(resolution,[],[f655,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    v3_ordinal1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.51    inference(flattening,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.51    inference(negated_conjecture,[],[f16])).
% 0.21/0.51  fof(f16,conjecture,(
% 0.21/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.21/0.51  fof(f655,plain,(
% 0.21/0.51    ~v3_ordinal1(sK0) | spl3_29),
% 0.21/0.51    inference(resolution,[],[f601,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0))) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f47,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f46,f66])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.21/0.51  fof(f601,plain,(
% 0.21/0.51    ~v3_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) | spl3_29),
% 0.21/0.51    inference(avatar_component_clause,[],[f599])).
% 0.21/0.51  fof(f599,plain,(
% 0.21/0.51    spl3_29 <=> v3_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.51  fof(f606,plain,(
% 0.21/0.51    ~spl3_29 | ~spl3_9 | ~spl3_30 | spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f596,f79,f603,f331,f599])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    spl3_2 <=> r1_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.51  fof(f596,plain,(
% 0.21/0.51    ~r1_tarski(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) | spl3_2),
% 0.21/0.51    inference(resolution,[],[f81,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ~r1_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1) | spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f79])).
% 0.21/0.51  fof(f595,plain,(
% 0.21/0.51    ~spl3_7 | ~spl3_9 | spl3_28 | spl3_27),
% 0.21/0.51    inference(avatar_split_clause,[],[f590,f585,f592,f331,f313])).
% 0.21/0.51  fof(f585,plain,(
% 0.21/0.51    spl3_27 <=> r1_ordinal1(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.51  fof(f590,plain,(
% 0.21/0.51    r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | spl3_27),
% 0.21/0.51    inference(resolution,[],[f587,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.21/0.51  fof(f587,plain,(
% 0.21/0.51    ~r1_ordinal1(sK1,sK0) | spl3_27),
% 0.21/0.51    inference(avatar_component_clause,[],[f585])).
% 0.21/0.51  fof(f588,plain,(
% 0.21/0.51    ~spl3_9 | ~spl3_7 | ~spl3_27 | ~spl3_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f581,f75,f585,f313,f331])).
% 0.21/0.51  fof(f581,plain,(
% 0.21/0.51    ~r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | ~spl3_1),
% 0.21/0.51    inference(resolution,[],[f580,f50])).
% 0.21/0.51  fof(f580,plain,(
% 0.21/0.51    ~r1_tarski(sK1,sK0) | ~spl3_1),
% 0.21/0.51    inference(resolution,[],[f76,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.51  fof(f572,plain,(
% 0.21/0.51    ~spl3_7 | spl3_1 | ~spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f569,f79,f75,f313])).
% 0.21/0.51  fof(f569,plain,(
% 0.21/0.51    r2_hidden(sK0,sK1) | ~v3_ordinal1(sK0) | ~spl3_2),
% 0.21/0.51    inference(resolution,[],[f442,f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    r1_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1) | ~spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f79])).
% 0.21/0.51  fof(f442,plain,(
% 0.21/0.51    ( ! [X1] : (~r1_ordinal1(k2_xboole_0(X1,k4_enumset1(X1,X1,X1,X1,X1,X1)),sK1) | r2_hidden(X1,sK1) | ~v3_ordinal1(X1)) )),
% 0.21/0.51    inference(resolution,[],[f369,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    v3_ordinal1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f369,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r1_ordinal1(k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)),X1) | r2_hidden(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(resolution,[],[f106,f71])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~v3_ordinal1(k2_xboole_0(X2,k4_enumset1(X2,X2,X2,X2,X2,X2))) | ~r1_ordinal1(k2_xboole_0(X2,k4_enumset1(X2,X2,X2,X2,X2,X2)),X3) | ~v3_ordinal1(X3) | r2_hidden(X2,X3)) )),
% 0.21/0.51    inference(resolution,[],[f86,f50])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(resolution,[],[f70,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f44,f67])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.21/0.51  fof(f345,plain,(
% 0.21/0.51    spl3_9),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f344])).
% 0.21/0.51  fof(f344,plain,(
% 0.21/0.51    $false | spl3_9),
% 0.21/0.51    inference(resolution,[],[f333,f41])).
% 0.21/0.51  fof(f333,plain,(
% 0.21/0.51    ~v3_ordinal1(sK1) | spl3_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f331])).
% 0.21/0.51  fof(f324,plain,(
% 0.21/0.51    spl3_7),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f323])).
% 0.21/0.51  fof(f323,plain,(
% 0.21/0.51    $false | spl3_7),
% 0.21/0.51    inference(resolution,[],[f315,f40])).
% 0.21/0.51  fof(f315,plain,(
% 0.21/0.51    ~v3_ordinal1(sK0) | spl3_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f313])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl3_1 | spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f69,f79,f75])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    r1_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1) | r2_hidden(sK0,sK1)),
% 0.21/0.51    inference(definition_unfolding,[],[f42,f67])).
% 0.21/0.51  % (22969)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ~spl3_1 | ~spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f68,f79,f75])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ~r1_ordinal1(k2_xboole_0(sK0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),sK1) | ~r2_hidden(sK0,sK1)),
% 0.21/0.51    inference(definition_unfolding,[],[f43,f67])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (22971)------------------------------
% 0.21/0.51  % (22971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22971)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (22971)Memory used [KB]: 6652
% 0.21/0.51  % (22971)Time elapsed: 0.084 s
% 0.21/0.51  % (22971)------------------------------
% 0.21/0.51  % (22971)------------------------------
% 0.21/0.51  % (22958)Success in time 0.157 s
%------------------------------------------------------------------------------
