%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:38 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 518 expanded)
%              Number of leaves         :   24 ( 177 expanded)
%              Depth                    :   20
%              Number of atoms          :  194 ( 687 expanded)
%              Number of equality atoms :   70 ( 491 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f398,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f76,f80,f85,f222,f397])).

fof(f397,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f395,f218,f83,f78,f74])).

fof(f74,plain,
    ( spl3_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f78,plain,
    ( spl3_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f83,plain,
    ( spl3_4
  <=> sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f218,plain,
    ( spl3_5
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f395,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl3_3
    | spl3_4
    | ~ spl3_5 ),
    inference(trivial_inequality_removal,[],[f393])).

fof(f393,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK0,sK1)
    | ~ spl3_3
    | spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f84,f354])).

fof(f354,plain,
    ( ! [X4,X3] :
        ( k3_tarski(k3_enumset1(X3,X3,X3,X3,k3_enumset1(X4,X4,X4,X4,X4))) = X3
        | ~ r2_hidden(X4,X3) )
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f353,f61])).

fof(f61,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f36,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f353,plain,
    ( ! [X4,X3] :
        ( k3_tarski(k3_enumset1(X3,X3,X3,X3,k3_enumset1(X4,X4,X4,X4,X4))) = k3_tarski(k3_enumset1(X3,X3,X3,X3,k1_xboole_0))
        | ~ r2_hidden(X4,X3) )
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f352,f243])).

fof(f243,plain,
    ( ! [X1] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(superposition,[],[f241,f207])).

fof(f207,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(global_subsumption,[],[f67,f204])).

fof(f204,plain,(
    ! [X0] :
      ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f195,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f195,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3)) = k5_xboole_0(X3,k3_xboole_0(X3,X3)) ),
    inference(superposition,[],[f63,f148])).

fof(f148,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f61,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f39,f57,f57])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

% (13859)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f63,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f43,f42,f42,f58])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

% (13846)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f241,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f234,f86])).

fof(f86,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_3 ),
    inference(resolution,[],[f38,f79])).

fof(f79,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f234,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k1_xboole_0,X0),k1_xboole_0)
        | k1_xboole_0 = k5_xboole_0(X0,X0) )
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f233,f219])).

fof(f219,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f218])).

fof(f233,plain,(
    ! [X0] :
      ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
      | r2_hidden(sK2(k1_xboole_0,X0),k1_xboole_0) ) ),
    inference(resolution,[],[f210,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f210,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ) ),
    inference(superposition,[],[f207,f45])).

fof(f352,plain,(
    ! [X4,X3] :
      ( k3_tarski(k3_enumset1(X3,X3,X3,X3,k3_enumset1(X4,X4,X4,X4,X4))) = k3_tarski(k3_enumset1(X3,X3,X3,X3,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_enumset1(X4,X4,X4,X4,X4)))))
      | ~ r2_hidden(X4,X3) ) ),
    inference(forward_demodulation,[],[f348,f207])).

fof(f348,plain,(
    ! [X4,X3] :
      ( k3_tarski(k3_enumset1(X3,X3,X3,X3,k3_enumset1(X4,X4,X4,X4,X4))) = k3_tarski(k3_enumset1(X3,X3,X3,X3,k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X4,X4,X4,X4,X4))))
      | ~ r2_hidden(X4,X3) ) ),
    inference(resolution,[],[f152,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f59])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f57])).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X0,X0))) ) ),
    inference(superposition,[],[f64,f45])).

fof(f64,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f44,f58,f42,f58])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f84,plain,
    ( sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f222,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f216,f218])).

fof(f216,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f155,f207])).

fof(f155,plain,(
    ! [X2] : k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) = X2 ),
    inference(forward_demodulation,[],[f153,f148])).

fof(f153,plain,(
    ! [X2] : k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)) ),
    inference(superposition,[],[f64,f148])).

fof(f85,plain,
    ( ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f81,f70,f83])).

fof(f70,plain,
    ( spl3_1
  <=> sK1 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f81,plain,
    ( sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl3_1 ),
    inference(forward_demodulation,[],[f71,f62])).

fof(f71,plain,
    ( sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f80,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f35,f78])).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f76,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f33,f74])).

fof(f33,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f72,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f60,f70])).

fof(f60,plain,(
    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f34,f58,f59])).

fof(f34,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n020.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 15:50:07 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.17/0.46  % (13856)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.17/0.46  % (13864)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.17/0.47  % (13856)Refutation not found, incomplete strategy% (13856)------------------------------
% 0.17/0.47  % (13856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.47  % (13849)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.17/0.47  % (13856)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.47  
% 0.17/0.47  % (13856)Memory used [KB]: 10618
% 0.17/0.47  % (13856)Time elapsed: 0.090 s
% 0.17/0.47  % (13856)------------------------------
% 0.17/0.47  % (13856)------------------------------
% 0.17/0.48  % (13873)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.17/0.49  % (13865)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.17/0.49  % (13857)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.17/0.50  % (13848)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.17/0.50  % (13864)Refutation found. Thanks to Tanya!
% 0.17/0.50  % SZS status Theorem for theBenchmark
% 0.17/0.50  % SZS output start Proof for theBenchmark
% 0.17/0.50  fof(f398,plain,(
% 0.17/0.50    $false),
% 0.17/0.50    inference(avatar_sat_refutation,[],[f72,f76,f80,f85,f222,f397])).
% 0.17/0.50  fof(f397,plain,(
% 0.17/0.50    ~spl3_2 | ~spl3_3 | spl3_4 | ~spl3_5),
% 0.17/0.50    inference(avatar_split_clause,[],[f395,f218,f83,f78,f74])).
% 0.17/0.50  fof(f74,plain,(
% 0.17/0.50    spl3_2 <=> r2_hidden(sK0,sK1)),
% 0.17/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.17/0.50  fof(f78,plain,(
% 0.17/0.50    spl3_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.17/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.17/0.50  fof(f83,plain,(
% 0.17/0.50    spl3_4 <=> sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 0.17/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.17/0.50  fof(f218,plain,(
% 0.17/0.50    spl3_5 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.17/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.17/0.50  fof(f395,plain,(
% 0.17/0.50    ~r2_hidden(sK0,sK1) | (~spl3_3 | spl3_4 | ~spl3_5)),
% 0.17/0.50    inference(trivial_inequality_removal,[],[f393])).
% 0.17/0.50  fof(f393,plain,(
% 0.17/0.50    sK1 != sK1 | ~r2_hidden(sK0,sK1) | (~spl3_3 | spl3_4 | ~spl3_5)),
% 0.17/0.50    inference(superposition,[],[f84,f354])).
% 0.17/0.50  fof(f354,plain,(
% 0.17/0.50    ( ! [X4,X3] : (k3_tarski(k3_enumset1(X3,X3,X3,X3,k3_enumset1(X4,X4,X4,X4,X4))) = X3 | ~r2_hidden(X4,X3)) ) | (~spl3_3 | ~spl3_5)),
% 0.17/0.50    inference(forward_demodulation,[],[f353,f61])).
% 0.17/0.50  fof(f61,plain,(
% 0.17/0.50    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 0.17/0.50    inference(definition_unfolding,[],[f36,f58])).
% 0.17/0.50  fof(f58,plain,(
% 0.17/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.17/0.50    inference(definition_unfolding,[],[f41,f57])).
% 0.17/0.50  fof(f57,plain,(
% 0.17/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.17/0.50    inference(definition_unfolding,[],[f40,f56])).
% 0.17/0.50  fof(f56,plain,(
% 0.17/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.17/0.50    inference(definition_unfolding,[],[f54,f55])).
% 0.17/0.50  fof(f55,plain,(
% 0.17/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.17/0.50    inference(cnf_transformation,[],[f14])).
% 0.17/0.50  fof(f14,axiom,(
% 0.17/0.50    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.17/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.17/0.50  fof(f54,plain,(
% 0.17/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.17/0.50    inference(cnf_transformation,[],[f13])).
% 0.17/0.50  fof(f13,axiom,(
% 0.17/0.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.17/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.17/0.50  fof(f40,plain,(
% 0.17/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.17/0.50    inference(cnf_transformation,[],[f12])).
% 0.17/0.50  fof(f12,axiom,(
% 0.17/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.17/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.17/0.50  fof(f41,plain,(
% 0.17/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.17/0.50    inference(cnf_transformation,[],[f16])).
% 0.17/0.50  fof(f16,axiom,(
% 0.17/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.17/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.17/0.50  fof(f36,plain,(
% 0.17/0.50    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.17/0.50    inference(cnf_transformation,[],[f6])).
% 0.17/0.50  fof(f6,axiom,(
% 0.17/0.50    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.17/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.17/0.50  fof(f353,plain,(
% 0.17/0.50    ( ! [X4,X3] : (k3_tarski(k3_enumset1(X3,X3,X3,X3,k3_enumset1(X4,X4,X4,X4,X4))) = k3_tarski(k3_enumset1(X3,X3,X3,X3,k1_xboole_0)) | ~r2_hidden(X4,X3)) ) | (~spl3_3 | ~spl3_5)),
% 0.17/0.50    inference(forward_demodulation,[],[f352,f243])).
% 0.17/0.50  fof(f243,plain,(
% 0.17/0.50    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) ) | (~spl3_3 | ~spl3_5)),
% 0.17/0.50    inference(superposition,[],[f241,f207])).
% 0.17/0.50  fof(f207,plain,(
% 0.17/0.50    ( ! [X0] : (k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 0.17/0.50    inference(global_subsumption,[],[f67,f204])).
% 0.17/0.50  fof(f204,plain,(
% 0.17/0.50    ( ! [X0] : (k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) | ~r1_tarski(X0,X0)) )),
% 0.17/0.50    inference(superposition,[],[f195,f45])).
% 0.17/0.50  fof(f45,plain,(
% 0.17/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.17/0.50    inference(cnf_transformation,[],[f22])).
% 0.17/0.50  fof(f22,plain,(
% 0.17/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.17/0.50    inference(ennf_transformation,[],[f7])).
% 0.17/0.50  fof(f7,axiom,(
% 0.17/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.17/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.17/0.50  fof(f195,plain,(
% 0.17/0.50    ( ! [X3] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3)) = k5_xboole_0(X3,k3_xboole_0(X3,X3))) )),
% 0.17/0.50    inference(superposition,[],[f63,f148])).
% 0.17/0.50  fof(f148,plain,(
% 0.17/0.50    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 0.17/0.50    inference(superposition,[],[f61,f62])).
% 0.17/0.50  fof(f62,plain,(
% 0.17/0.50    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 0.17/0.50    inference(definition_unfolding,[],[f39,f57,f57])).
% 0.17/0.50  fof(f39,plain,(
% 0.17/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.17/0.50    inference(cnf_transformation,[],[f10])).
% 0.17/0.50  fof(f10,axiom,(
% 0.17/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.17/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.17/0.50  % (13859)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.17/0.50  fof(f63,plain,(
% 0.17/0.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 0.17/0.50    inference(definition_unfolding,[],[f43,f42,f42,f58])).
% 0.17/0.50  fof(f42,plain,(
% 0.17/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.17/0.50    inference(cnf_transformation,[],[f5])).
% 0.17/0.50  fof(f5,axiom,(
% 0.17/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.17/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.17/0.50  fof(f43,plain,(
% 0.17/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.17/0.50    inference(cnf_transformation,[],[f9])).
% 0.17/0.50  fof(f9,axiom,(
% 0.17/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.17/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.17/0.50  % (13846)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.17/0.50  fof(f67,plain,(
% 0.17/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.17/0.50    inference(equality_resolution,[],[f47])).
% 0.17/0.50  fof(f47,plain,(
% 0.17/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.17/0.50    inference(cnf_transformation,[],[f27])).
% 0.17/0.50  fof(f27,plain,(
% 0.17/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.17/0.50    inference(flattening,[],[f26])).
% 0.17/0.50  fof(f26,plain,(
% 0.17/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.17/0.50    inference(nnf_transformation,[],[f4])).
% 0.17/0.50  fof(f4,axiom,(
% 0.17/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.17/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.17/0.50  fof(f241,plain,(
% 0.17/0.50    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | (~spl3_3 | ~spl3_5)),
% 0.17/0.50    inference(resolution,[],[f234,f86])).
% 0.17/0.50  fof(f86,plain,(
% 0.17/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl3_3),
% 0.17/0.50    inference(resolution,[],[f38,f79])).
% 0.17/0.50  fof(f79,plain,(
% 0.17/0.50    v1_xboole_0(k1_xboole_0) | ~spl3_3),
% 0.17/0.50    inference(avatar_component_clause,[],[f78])).
% 0.17/0.51  fof(f38,plain,(
% 0.17/0.51    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.17/0.51    inference(cnf_transformation,[],[f21])).
% 0.17/0.51  fof(f21,plain,(
% 0.17/0.51    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.17/0.51    inference(ennf_transformation,[],[f19])).
% 0.17/0.51  fof(f19,plain,(
% 0.17/0.51    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.17/0.51    inference(unused_predicate_definition_removal,[],[f1])).
% 0.17/0.51  fof(f1,axiom,(
% 0.17/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.17/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.17/0.51  fof(f234,plain,(
% 0.17/0.51    ( ! [X0] : (r2_hidden(sK2(k1_xboole_0,X0),k1_xboole_0) | k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl3_5),
% 0.17/0.51    inference(forward_demodulation,[],[f233,f219])).
% 0.17/0.51  fof(f219,plain,(
% 0.17/0.51    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_5),
% 0.17/0.51    inference(avatar_component_clause,[],[f218])).
% 0.17/0.51  fof(f233,plain,(
% 0.17/0.51    ( ! [X0] : (k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) | r2_hidden(sK2(k1_xboole_0,X0),k1_xboole_0)) )),
% 0.17/0.51    inference(resolution,[],[f210,f50])).
% 0.17/0.51  fof(f50,plain,(
% 0.17/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.17/0.51    inference(cnf_transformation,[],[f31])).
% 0.17/0.51  fof(f31,plain,(
% 0.17/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.17/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 0.17/0.51  fof(f30,plain,(
% 0.17/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.17/0.51    introduced(choice_axiom,[])).
% 0.17/0.51  fof(f29,plain,(
% 0.17/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.17/0.51    inference(rectify,[],[f28])).
% 0.17/0.51  fof(f28,plain,(
% 0.17/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.17/0.51    inference(nnf_transformation,[],[f23])).
% 0.17/0.51  fof(f23,plain,(
% 0.17/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.17/0.51    inference(ennf_transformation,[],[f2])).
% 0.17/0.51  fof(f2,axiom,(
% 0.17/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.17/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.17/0.51  fof(f210,plain,(
% 0.17/0.51    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 0.17/0.51    inference(superposition,[],[f207,f45])).
% 0.17/0.51  fof(f352,plain,(
% 0.17/0.51    ( ! [X4,X3] : (k3_tarski(k3_enumset1(X3,X3,X3,X3,k3_enumset1(X4,X4,X4,X4,X4))) = k3_tarski(k3_enumset1(X3,X3,X3,X3,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_enumset1(X4,X4,X4,X4,X4))))) | ~r2_hidden(X4,X3)) )),
% 0.17/0.51    inference(forward_demodulation,[],[f348,f207])).
% 0.17/0.51  fof(f348,plain,(
% 0.17/0.51    ( ! [X4,X3] : (k3_tarski(k3_enumset1(X3,X3,X3,X3,k3_enumset1(X4,X4,X4,X4,X4))) = k3_tarski(k3_enumset1(X3,X3,X3,X3,k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X4,X4,X4,X4,X4)))) | ~r2_hidden(X4,X3)) )),
% 0.17/0.51    inference(resolution,[],[f152,f65])).
% 0.17/0.51  fof(f65,plain,(
% 0.17/0.51    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.17/0.51    inference(definition_unfolding,[],[f53,f59])).
% 0.17/0.51  fof(f59,plain,(
% 0.17/0.51    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.17/0.51    inference(definition_unfolding,[],[f37,f57])).
% 0.17/0.51  fof(f37,plain,(
% 0.17/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.17/0.51    inference(cnf_transformation,[],[f11])).
% 0.17/0.51  fof(f11,axiom,(
% 0.17/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.17/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.17/0.51  fof(f53,plain,(
% 0.17/0.51    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.17/0.51    inference(cnf_transformation,[],[f32])).
% 0.17/0.51  fof(f32,plain,(
% 0.17/0.51    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.17/0.51    inference(nnf_transformation,[],[f15])).
% 0.17/0.51  fof(f15,axiom,(
% 0.17/0.51    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.17/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.17/0.51  fof(f152,plain,(
% 0.17/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X0,X0)))) )),
% 0.17/0.51    inference(superposition,[],[f64,f45])).
% 0.17/0.51  fof(f64,plain,(
% 0.17/0.51    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 0.17/0.51    inference(definition_unfolding,[],[f44,f58,f42,f58])).
% 0.17/0.51  fof(f44,plain,(
% 0.17/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.17/0.51    inference(cnf_transformation,[],[f8])).
% 0.17/0.51  fof(f8,axiom,(
% 0.17/0.51    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.17/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.17/0.51  fof(f84,plain,(
% 0.17/0.51    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl3_4),
% 0.17/0.51    inference(avatar_component_clause,[],[f83])).
% 0.17/0.51  fof(f222,plain,(
% 0.17/0.51    spl3_5),
% 0.17/0.51    inference(avatar_split_clause,[],[f216,f218])).
% 0.17/0.51  fof(f216,plain,(
% 0.17/0.51    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.17/0.51    inference(superposition,[],[f155,f207])).
% 0.17/0.51  fof(f155,plain,(
% 0.17/0.51    ( ! [X2] : (k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) = X2) )),
% 0.17/0.51    inference(forward_demodulation,[],[f153,f148])).
% 0.17/0.51  fof(f153,plain,(
% 0.17/0.51    ( ! [X2] : (k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2))) )),
% 0.17/0.51    inference(superposition,[],[f64,f148])).
% 0.17/0.51  fof(f85,plain,(
% 0.17/0.51    ~spl3_4 | spl3_1),
% 0.17/0.51    inference(avatar_split_clause,[],[f81,f70,f83])).
% 0.17/0.51  fof(f70,plain,(
% 0.17/0.51    spl3_1 <=> sK1 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 0.17/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.17/0.51  fof(f81,plain,(
% 0.17/0.51    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl3_1),
% 0.17/0.51    inference(forward_demodulation,[],[f71,f62])).
% 0.17/0.51  fof(f71,plain,(
% 0.17/0.51    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) | spl3_1),
% 0.17/0.51    inference(avatar_component_clause,[],[f70])).
% 0.17/0.51  fof(f80,plain,(
% 0.17/0.51    spl3_3),
% 0.17/0.51    inference(avatar_split_clause,[],[f35,f78])).
% 0.17/0.51  fof(f35,plain,(
% 0.17/0.51    v1_xboole_0(k1_xboole_0)),
% 0.17/0.51    inference(cnf_transformation,[],[f3])).
% 0.17/0.51  fof(f3,axiom,(
% 0.17/0.51    v1_xboole_0(k1_xboole_0)),
% 0.17/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.17/0.51  fof(f76,plain,(
% 0.17/0.51    spl3_2),
% 0.17/0.51    inference(avatar_split_clause,[],[f33,f74])).
% 0.17/0.51  fof(f33,plain,(
% 0.17/0.51    r2_hidden(sK0,sK1)),
% 0.17/0.51    inference(cnf_transformation,[],[f25])).
% 0.17/0.51  fof(f25,plain,(
% 0.17/0.51    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 0.17/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f24])).
% 0.17/0.51  fof(f24,plain,(
% 0.17/0.51    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 0.17/0.51    introduced(choice_axiom,[])).
% 0.17/0.51  fof(f20,plain,(
% 0.17/0.51    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 0.17/0.51    inference(ennf_transformation,[],[f18])).
% 0.17/0.51  fof(f18,negated_conjecture,(
% 0.17/0.51    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.17/0.51    inference(negated_conjecture,[],[f17])).
% 0.17/0.51  fof(f17,conjecture,(
% 0.17/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.17/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 0.17/0.51  fof(f72,plain,(
% 0.17/0.51    ~spl3_1),
% 0.17/0.51    inference(avatar_split_clause,[],[f60,f70])).
% 0.17/0.51  fof(f60,plain,(
% 0.17/0.51    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 0.17/0.51    inference(definition_unfolding,[],[f34,f58,f59])).
% 0.17/0.51  fof(f34,plain,(
% 0.17/0.51    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.17/0.51    inference(cnf_transformation,[],[f25])).
% 0.17/0.51  % SZS output end Proof for theBenchmark
% 0.17/0.51  % (13864)------------------------------
% 0.17/0.51  % (13864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.51  % (13864)Termination reason: Refutation
% 0.17/0.51  
% 0.17/0.51  % (13864)Memory used [KB]: 11001
% 0.17/0.51  % (13864)Time elapsed: 0.131 s
% 0.17/0.51  % (13864)------------------------------
% 0.17/0.51  % (13864)------------------------------
% 0.17/0.51  % (13865)Refutation not found, incomplete strategy% (13865)------------------------------
% 0.17/0.51  % (13865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.51  % (13844)Success in time 0.178 s
%------------------------------------------------------------------------------
