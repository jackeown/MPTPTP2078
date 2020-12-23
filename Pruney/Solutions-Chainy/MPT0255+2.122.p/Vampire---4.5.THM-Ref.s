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
% DateTime   : Thu Dec  3 12:39:50 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 218 expanded)
%              Number of leaves         :   24 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  265 ( 513 expanded)
%              Number of equality atoms :   56 ( 131 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f591,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f436,f465,f590])).

fof(f590,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f585])).

fof(f585,plain,
    ( $false
    | ~ spl7_3 ),
    inference(resolution,[],[f584,f44])).

fof(f44,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f584,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_3 ),
    inference(resolution,[],[f574,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f574,plain,
    ( r2_hidden(sK5(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl7_3 ),
    inference(resolution,[],[f573,f44])).

fof(f573,plain,
    ( ! [X11] :
        ( ~ v1_xboole_0(X11)
        | r2_hidden(sK5(o_0_0_xboole_0,X11),o_0_0_xboole_0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f531,f48])).

fof(f531,plain,
    ( ! [X0] :
        ( r2_hidden(sK2,X0)
        | r2_hidden(sK5(o_0_0_xboole_0,X0),o_0_0_xboole_0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f479,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f479,plain,
    ( ! [X2] :
        ( ~ r1_tarski(o_0_0_xboole_0,X2)
        | r2_hidden(sK2,X2) )
    | ~ spl7_3 ),
    inference(superposition,[],[f84,f431])).

fof(f431,plain,
    ( o_0_0_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f429])).

fof(f429,plain,
    ( spl7_3
  <=> o_0_0_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f68,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f75])).

% (3320)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f70,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

% (3321)Refutation not found, incomplete strategy% (3321)------------------------------
% (3321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3321)Termination reason: Refutation not found, incomplete strategy

% (3321)Memory used [KB]: 10618
% (3321)Time elapsed: 0.140 s
% (3321)------------------------------
% (3321)------------------------------
fof(f58,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f465,plain,(
    ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f460])).

fof(f460,plain,
    ( $false
    | ~ spl7_4 ),
    inference(resolution,[],[f443,f44])).

fof(f443,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_4 ),
    inference(resolution,[],[f435,f48])).

fof(f435,plain,
    ( r2_hidden(sK4(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),o_0_0_xboole_0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f433])).

fof(f433,plain,
    ( spl7_4
  <=> r2_hidden(sK4(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f436,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f427,f433,f429])).

fof(f427,plain,
    ( r2_hidden(sK4(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),o_0_0_xboole_0)
    | o_0_0_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f423])).

fof(f423,plain,
    ( r2_hidden(sK4(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),o_0_0_xboole_0)
    | r2_hidden(sK4(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),o_0_0_xboole_0)
    | o_0_0_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    inference(resolution,[],[f417,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | r2_hidden(sK4(X0),X2)
      | r2_hidden(sK4(X0),X1)
      | o_0_0_xboole_0 = X0 ) ),
    inference(resolution,[],[f61,f107])).

fof(f107,plain,(
    ! [X2] :
      ( r2_hidden(sK4(X2),X2)
      | o_0_0_xboole_0 = X2 ) ),
    inference(resolution,[],[f103,f96])).

fof(f96,plain,(
    ! [X0] : sP0(o_0_0_xboole_0,X0,X0) ),
    inference(forward_demodulation,[],[f95,f90])).

fof(f90,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f46,f87])).

fof(f87,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[],[f47,f44])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f95,plain,(
    ! [X0] : sP0(o_0_0_xboole_0,X0,k5_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(superposition,[],[f86,f91])).

fof(f91,plain,(
    ! [X0] : o_0_0_xboole_0 = k3_xboole_0(X0,o_0_0_xboole_0) ),
    inference(backward_demodulation,[],[f45,f87])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f86,plain,(
    ! [X0,X1] : sP0(X1,X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f65,f53])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f24])).

% (3313)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f23])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(sK4(X2),X1)
      | o_0_0_xboole_0 = X2 ) ),
    inference(resolution,[],[f98,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f47,f87])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ sP0(X2,X1,X0)
      | r2_hidden(sK4(X0),X1) ) ),
    inference(resolution,[],[f59,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
              & r2_hidden(sK6(X0,X1,X2),X1) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f417,plain,(
    sP0(o_0_0_xboole_0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),o_0_0_xboole_0) ),
    inference(superposition,[],[f128,f92])).

fof(f92,plain,(
    o_0_0_xboole_0 = k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),sK3)) ),
    inference(backward_demodulation,[],[f78,f87])).

% (3322)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f78,plain,(
    k1_xboole_0 = k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f43,f77,f76])).

fof(f77,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f76])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f43,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f128,plain,(
    ! [X0,X1] : sP0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0,o_0_0_xboole_0) ),
    inference(superposition,[],[f86,f88])).

fof(f88,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(backward_demodulation,[],[f79,f87])).

fof(f79,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f50,f53,f77])).

fof(f50,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (3316)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.49  % (3327)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.50  % (3332)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.50  % (3308)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.51  % (3315)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.51  % (3315)Refutation not found, incomplete strategy% (3315)------------------------------
% 0.19/0.51  % (3315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (3315)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (3315)Memory used [KB]: 10618
% 0.19/0.51  % (3315)Time elapsed: 0.109 s
% 0.19/0.51  % (3315)------------------------------
% 0.19/0.51  % (3315)------------------------------
% 0.19/0.51  % (3317)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.25/0.51  % (3326)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.25/0.51  % (3311)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.25/0.51  % (3319)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.25/0.52  % (3308)Refutation not found, incomplete strategy% (3308)------------------------------
% 1.25/0.52  % (3308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (3308)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (3308)Memory used [KB]: 6140
% 1.25/0.52  % (3308)Time elapsed: 0.120 s
% 1.25/0.52  % (3308)------------------------------
% 1.25/0.52  % (3308)------------------------------
% 1.25/0.52  % (3319)Refutation not found, incomplete strategy% (3319)------------------------------
% 1.25/0.52  % (3319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (3316)Refutation found. Thanks to Tanya!
% 1.25/0.52  % SZS status Theorem for theBenchmark
% 1.25/0.52  % (3310)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.25/0.52  % (3324)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.25/0.52  % (3305)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.25/0.52  % (3319)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (3319)Memory used [KB]: 6140
% 1.25/0.52  % (3319)Time elapsed: 0.004 s
% 1.25/0.52  % (3319)------------------------------
% 1.25/0.52  % (3319)------------------------------
% 1.25/0.52  % (3331)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.25/0.52  % (3323)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.25/0.52  % (3324)Refutation not found, incomplete strategy% (3324)------------------------------
% 1.25/0.52  % (3324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (3307)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.25/0.52  % (3329)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.25/0.53  % (3318)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.25/0.53  % (3306)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.25/0.53  % (3324)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (3324)Memory used [KB]: 10746
% 1.25/0.53  % (3324)Time elapsed: 0.113 s
% 1.25/0.53  % (3324)------------------------------
% 1.25/0.53  % (3324)------------------------------
% 1.25/0.53  % (3309)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.42/0.53  % (3328)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.42/0.53  % (3304)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.42/0.53  % (3330)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.42/0.53  % (3321)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.42/0.53  % SZS output start Proof for theBenchmark
% 1.42/0.53  fof(f591,plain,(
% 1.42/0.53    $false),
% 1.42/0.53    inference(avatar_sat_refutation,[],[f436,f465,f590])).
% 1.42/0.53  fof(f590,plain,(
% 1.42/0.53    ~spl7_3),
% 1.42/0.53    inference(avatar_contradiction_clause,[],[f585])).
% 1.42/0.53  fof(f585,plain,(
% 1.42/0.53    $false | ~spl7_3),
% 1.42/0.53    inference(resolution,[],[f584,f44])).
% 1.42/0.53  fof(f44,plain,(
% 1.42/0.53    v1_xboole_0(o_0_0_xboole_0)),
% 1.42/0.53    inference(cnf_transformation,[],[f4])).
% 1.42/0.53  fof(f4,axiom,(
% 1.42/0.53    v1_xboole_0(o_0_0_xboole_0)),
% 1.42/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 1.42/0.53  fof(f584,plain,(
% 1.42/0.53    ~v1_xboole_0(o_0_0_xboole_0) | ~spl7_3),
% 1.42/0.53    inference(resolution,[],[f574,f48])).
% 1.42/0.53  fof(f48,plain,(
% 1.42/0.53    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.42/0.53    inference(cnf_transformation,[],[f30])).
% 1.42/0.53  fof(f30,plain,(
% 1.42/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.42/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 1.42/0.53  fof(f29,plain,(
% 1.42/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.42/0.53    introduced(choice_axiom,[])).
% 1.42/0.53  fof(f28,plain,(
% 1.42/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.42/0.53    inference(rectify,[],[f27])).
% 1.42/0.53  fof(f27,plain,(
% 1.42/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.42/0.53    inference(nnf_transformation,[],[f1])).
% 1.42/0.53  fof(f1,axiom,(
% 1.42/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.42/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.42/0.53  fof(f574,plain,(
% 1.42/0.53    r2_hidden(sK5(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) | ~spl7_3),
% 1.42/0.53    inference(resolution,[],[f573,f44])).
% 1.42/0.53  fof(f573,plain,(
% 1.42/0.53    ( ! [X11] : (~v1_xboole_0(X11) | r2_hidden(sK5(o_0_0_xboole_0,X11),o_0_0_xboole_0)) ) | ~spl7_3),
% 1.42/0.53    inference(resolution,[],[f531,f48])).
% 1.42/0.53  fof(f531,plain,(
% 1.42/0.53    ( ! [X0] : (r2_hidden(sK2,X0) | r2_hidden(sK5(o_0_0_xboole_0,X0),o_0_0_xboole_0)) ) | ~spl7_3),
% 1.42/0.53    inference(resolution,[],[f479,f56])).
% 1.42/0.53  fof(f56,plain,(
% 1.42/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 1.42/0.53    inference(cnf_transformation,[],[f34])).
% 1.42/0.53  fof(f34,plain,(
% 1.42/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.42/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).
% 1.42/0.53  fof(f33,plain,(
% 1.42/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.42/0.53    introduced(choice_axiom,[])).
% 1.42/0.53  fof(f32,plain,(
% 1.42/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.42/0.53    inference(rectify,[],[f31])).
% 1.42/0.53  fof(f31,plain,(
% 1.42/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.42/0.53    inference(nnf_transformation,[],[f22])).
% 1.42/0.53  fof(f22,plain,(
% 1.42/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.42/0.53    inference(ennf_transformation,[],[f2])).
% 1.42/0.53  fof(f2,axiom,(
% 1.42/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.42/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.42/0.53  fof(f479,plain,(
% 1.42/0.53    ( ! [X2] : (~r1_tarski(o_0_0_xboole_0,X2) | r2_hidden(sK2,X2)) ) | ~spl7_3),
% 1.42/0.53    inference(superposition,[],[f84,f431])).
% 1.42/0.53  fof(f431,plain,(
% 1.42/0.53    o_0_0_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) | ~spl7_3),
% 1.42/0.53    inference(avatar_component_clause,[],[f429])).
% 1.42/0.53  fof(f429,plain,(
% 1.42/0.53    spl7_3 <=> o_0_0_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),
% 1.42/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.42/0.53  fof(f84,plain,(
% 1.42/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 1.42/0.53    inference(definition_unfolding,[],[f68,f76])).
% 1.42/0.53  fof(f76,plain,(
% 1.42/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.42/0.53    inference(definition_unfolding,[],[f52,f75])).
% 1.42/0.53  % (3320)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.42/0.53  fof(f75,plain,(
% 1.42/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 1.42/0.53    inference(definition_unfolding,[],[f58,f74])).
% 1.42/0.54  fof(f74,plain,(
% 1.42/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 1.42/0.54    inference(definition_unfolding,[],[f70,f73])).
% 1.42/0.54  fof(f73,plain,(
% 1.42/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 1.42/0.54    inference(definition_unfolding,[],[f71,f72])).
% 1.42/0.54  fof(f72,plain,(
% 1.42/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f15])).
% 1.42/0.54  fof(f15,axiom,(
% 1.42/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.42/0.54  fof(f71,plain,(
% 1.42/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f14])).
% 1.42/0.54  fof(f14,axiom,(
% 1.42/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.42/0.54  fof(f70,plain,(
% 1.42/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f13])).
% 1.42/0.54  fof(f13,axiom,(
% 1.42/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.42/0.54  % (3321)Refutation not found, incomplete strategy% (3321)------------------------------
% 1.42/0.54  % (3321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (3321)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (3321)Memory used [KB]: 10618
% 1.42/0.54  % (3321)Time elapsed: 0.140 s
% 1.42/0.54  % (3321)------------------------------
% 1.42/0.54  % (3321)------------------------------
% 1.42/0.54  fof(f58,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f12])).
% 1.42/0.54  fof(f12,axiom,(
% 1.42/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.42/0.54  fof(f52,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f11])).
% 1.42/0.54  fof(f11,axiom,(
% 1.42/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.42/0.54  fof(f68,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f42])).
% 1.42/0.54  fof(f42,plain,(
% 1.42/0.54    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.42/0.54    inference(flattening,[],[f41])).
% 1.42/0.54  fof(f41,plain,(
% 1.42/0.54    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.42/0.54    inference(nnf_transformation,[],[f17])).
% 1.42/0.54  fof(f17,axiom,(
% 1.42/0.54    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.42/0.54  fof(f465,plain,(
% 1.42/0.54    ~spl7_4),
% 1.42/0.54    inference(avatar_contradiction_clause,[],[f460])).
% 1.42/0.54  fof(f460,plain,(
% 1.42/0.54    $false | ~spl7_4),
% 1.42/0.54    inference(resolution,[],[f443,f44])).
% 1.42/0.54  fof(f443,plain,(
% 1.42/0.54    ~v1_xboole_0(o_0_0_xboole_0) | ~spl7_4),
% 1.42/0.54    inference(resolution,[],[f435,f48])).
% 1.42/0.54  fof(f435,plain,(
% 1.42/0.54    r2_hidden(sK4(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),o_0_0_xboole_0) | ~spl7_4),
% 1.42/0.54    inference(avatar_component_clause,[],[f433])).
% 1.42/0.54  fof(f433,plain,(
% 1.42/0.54    spl7_4 <=> r2_hidden(sK4(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),o_0_0_xboole_0)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.42/0.54  fof(f436,plain,(
% 1.42/0.54    spl7_3 | spl7_4),
% 1.42/0.54    inference(avatar_split_clause,[],[f427,f433,f429])).
% 1.42/0.54  fof(f427,plain,(
% 1.42/0.54    r2_hidden(sK4(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),o_0_0_xboole_0) | o_0_0_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),
% 1.42/0.54    inference(duplicate_literal_removal,[],[f423])).
% 1.42/0.54  fof(f423,plain,(
% 1.42/0.54    r2_hidden(sK4(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),o_0_0_xboole_0) | r2_hidden(sK4(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),o_0_0_xboole_0) | o_0_0_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),
% 1.42/0.54    inference(resolution,[],[f417,f116])).
% 1.42/0.54  fof(f116,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | r2_hidden(sK4(X0),X2) | r2_hidden(sK4(X0),X1) | o_0_0_xboole_0 = X0) )),
% 1.42/0.54    inference(resolution,[],[f61,f107])).
% 1.42/0.54  fof(f107,plain,(
% 1.42/0.54    ( ! [X2] : (r2_hidden(sK4(X2),X2) | o_0_0_xboole_0 = X2) )),
% 1.42/0.54    inference(resolution,[],[f103,f96])).
% 1.42/0.54  fof(f96,plain,(
% 1.42/0.54    ( ! [X0] : (sP0(o_0_0_xboole_0,X0,X0)) )),
% 1.42/0.54    inference(forward_demodulation,[],[f95,f90])).
% 1.42/0.54  fof(f90,plain,(
% 1.42/0.54    ( ! [X0] : (k5_xboole_0(X0,o_0_0_xboole_0) = X0) )),
% 1.42/0.54    inference(backward_demodulation,[],[f46,f87])).
% 1.42/0.54  fof(f87,plain,(
% 1.42/0.54    o_0_0_xboole_0 = k1_xboole_0),
% 1.42/0.54    inference(resolution,[],[f47,f44])).
% 1.42/0.54  fof(f47,plain,(
% 1.42/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.42/0.54    inference(cnf_transformation,[],[f21])).
% 1.42/0.54  fof(f21,plain,(
% 1.42/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.42/0.54    inference(ennf_transformation,[],[f5])).
% 1.42/0.54  fof(f5,axiom,(
% 1.42/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.42/0.54  fof(f46,plain,(
% 1.42/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.42/0.54    inference(cnf_transformation,[],[f9])).
% 1.42/0.54  fof(f9,axiom,(
% 1.42/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.42/0.54  fof(f95,plain,(
% 1.42/0.54    ( ! [X0] : (sP0(o_0_0_xboole_0,X0,k5_xboole_0(X0,o_0_0_xboole_0))) )),
% 1.42/0.54    inference(superposition,[],[f86,f91])).
% 1.42/0.54  fof(f91,plain,(
% 1.42/0.54    ( ! [X0] : (o_0_0_xboole_0 = k3_xboole_0(X0,o_0_0_xboole_0)) )),
% 1.42/0.54    inference(backward_demodulation,[],[f45,f87])).
% 1.42/0.54  fof(f45,plain,(
% 1.42/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f7])).
% 1.42/0.54  fof(f7,axiom,(
% 1.42/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.42/0.54  fof(f86,plain,(
% 1.42/0.54    ( ! [X0,X1] : (sP0(X1,X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.42/0.54    inference(equality_resolution,[],[f82])).
% 1.42/0.54  fof(f82,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.42/0.54    inference(definition_unfolding,[],[f65,f53])).
% 1.42/0.54  fof(f53,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f6])).
% 1.42/0.54  fof(f6,axiom,(
% 1.42/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.42/0.54  fof(f65,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.42/0.54    inference(cnf_transformation,[],[f40])).
% 1.42/0.54  fof(f40,plain,(
% 1.42/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.42/0.54    inference(nnf_transformation,[],[f24])).
% 1.42/0.54  % (3313)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.42/0.54  fof(f24,plain,(
% 1.42/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.42/0.54    inference(definition_folding,[],[f3,f23])).
% 1.42/0.54  fof(f23,plain,(
% 1.42/0.54    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.42/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.42/0.54  fof(f3,axiom,(
% 1.42/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.42/0.54  fof(f103,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(sK4(X2),X1) | o_0_0_xboole_0 = X2) )),
% 1.42/0.54    inference(resolution,[],[f98,f89])).
% 1.42/0.54  fof(f89,plain,(
% 1.42/0.54    ( ! [X0] : (~v1_xboole_0(X0) | o_0_0_xboole_0 = X0) )),
% 1.42/0.54    inference(backward_demodulation,[],[f47,f87])).
% 1.42/0.54  fof(f98,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~sP0(X2,X1,X0) | r2_hidden(sK4(X0),X1)) )),
% 1.42/0.54    inference(resolution,[],[f59,f49])).
% 1.42/0.54  fof(f49,plain,(
% 1.42/0.54    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f30])).
% 1.42/0.54  fof(f59,plain,(
% 1.42/0.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~sP0(X0,X1,X2)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f39])).
% 1.42/0.54  fof(f39,plain,(
% 1.42/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.42/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f38])).
% 1.42/0.54  fof(f38,plain,(
% 1.42/0.54    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f37,plain,(
% 1.42/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.42/0.54    inference(rectify,[],[f36])).
% 1.42/0.54  fof(f36,plain,(
% 1.42/0.54    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.42/0.54    inference(flattening,[],[f35])).
% 1.42/0.54  fof(f35,plain,(
% 1.42/0.54    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.42/0.54    inference(nnf_transformation,[],[f23])).
% 1.42/0.54  fof(f61,plain,(
% 1.42/0.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | r2_hidden(X4,X0) | r2_hidden(X4,X2) | ~sP0(X0,X1,X2)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f39])).
% 1.42/0.54  fof(f417,plain,(
% 1.42/0.54    sP0(o_0_0_xboole_0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),o_0_0_xboole_0)),
% 1.42/0.54    inference(superposition,[],[f128,f92])).
% 1.42/0.54  fof(f92,plain,(
% 1.42/0.54    o_0_0_xboole_0 = k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),sK3))),
% 1.42/0.54    inference(backward_demodulation,[],[f78,f87])).
% 1.42/0.54  % (3322)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.42/0.54  fof(f78,plain,(
% 1.42/0.54    k1_xboole_0 = k3_tarski(k5_enumset1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),sK3))),
% 1.42/0.54    inference(definition_unfolding,[],[f43,f77,f76])).
% 1.42/0.54  fof(f77,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 1.42/0.54    inference(definition_unfolding,[],[f51,f76])).
% 1.42/0.54  fof(f51,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f16])).
% 1.42/0.54  fof(f16,axiom,(
% 1.42/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.42/0.54  fof(f43,plain,(
% 1.42/0.54    k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 1.42/0.54    inference(cnf_transformation,[],[f26])).
% 1.42/0.54  fof(f26,plain,(
% 1.42/0.54    k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 1.42/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f25])).
% 1.42/0.54  fof(f25,plain,(
% 1.42/0.54    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f20,plain,(
% 1.42/0.54    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.42/0.54    inference(ennf_transformation,[],[f19])).
% 1.42/0.54  fof(f19,negated_conjecture,(
% 1.42/0.54    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.42/0.54    inference(negated_conjecture,[],[f18])).
% 1.42/0.54  fof(f18,conjecture,(
% 1.42/0.54    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 1.42/0.54  fof(f128,plain,(
% 1.42/0.54    ( ! [X0,X1] : (sP0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0,o_0_0_xboole_0)) )),
% 1.42/0.54    inference(superposition,[],[f86,f88])).
% 1.42/0.54  fof(f88,plain,(
% 1.42/0.54    ( ! [X0,X1] : (o_0_0_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))) )),
% 1.42/0.54    inference(backward_demodulation,[],[f79,f87])).
% 1.42/0.54  fof(f79,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))) )),
% 1.42/0.54    inference(definition_unfolding,[],[f50,f53,f77])).
% 1.42/0.54  fof(f50,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f8])).
% 1.42/0.54  fof(f8,axiom,(
% 1.42/0.54    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.42/0.54  % SZS output end Proof for theBenchmark
% 1.42/0.54  % (3316)------------------------------
% 1.42/0.54  % (3316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (3316)Termination reason: Refutation
% 1.42/0.54  
% 1.42/0.54  % (3316)Memory used [KB]: 6524
% 1.42/0.54  % (3316)Time elapsed: 0.121 s
% 1.42/0.54  % (3316)------------------------------
% 1.42/0.54  % (3316)------------------------------
% 1.42/0.54  % (3303)Success in time 0.185 s
%------------------------------------------------------------------------------
