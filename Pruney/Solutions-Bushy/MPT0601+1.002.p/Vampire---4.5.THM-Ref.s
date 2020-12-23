%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0601+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:17 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 145 expanded)
%              Number of leaves         :   22 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :  255 ( 445 expanded)
%              Number of equality atoms :   42 (  92 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f135,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f54,f58,f62,f67,f84,f94,f103,f110,f128,f134])).

fof(f134,plain,
    ( ~ spl6_4
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f132,f126,f60])).

fof(f60,plain,
    ( spl6_4
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f126,plain,
    ( spl6_13
  <=> r2_hidden(sK5(sK1,sK0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f132,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl6_13 ),
    inference(resolution,[],[f127,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f127,plain,
    ( r2_hidden(sK5(sK1,sK0),o_0_0_xboole_0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f126])).

fof(f128,plain,
    ( ~ spl6_3
    | spl6_13
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f124,f108,f100,f126,f56])).

fof(f56,plain,
    ( spl6_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f100,plain,
    ( spl6_9
  <=> o_0_0_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f108,plain,
    ( spl6_10
  <=> r2_hidden(k4_tarski(sK0,sK5(sK1,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f124,plain,
    ( r2_hidden(sK5(sK1,sK0),o_0_0_xboole_0)
    | ~ v1_relat_1(sK1)
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f121,f101])).

fof(f101,plain,
    ( o_0_0_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f121,plain,
    ( r2_hidden(sK5(sK1,sK0),k11_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl6_10 ),
    inference(resolution,[],[f109,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f109,plain,
    ( r2_hidden(k4_tarski(sK0,sK5(sK1,sK0)),sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f110,plain,
    ( spl6_10
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f105,f46,f108])).

fof(f46,plain,
    ( spl6_1
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f105,plain,
    ( r2_hidden(k4_tarski(sK0,sK5(sK1,sK0)),sK1)
    | ~ spl6_1 ),
    inference(resolution,[],[f52,f44])).

fof(f44,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f23,f26,f25,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f52,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f103,plain,
    ( spl6_9
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f102,f65,f49,f100])).

fof(f49,plain,
    ( spl6_2
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f65,plain,
    ( spl6_5
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f102,plain,
    ( o_0_0_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f50,f66])).

% (8592)Refutation not found, incomplete strategy% (8592)------------------------------
% (8592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8592)Termination reason: Refutation not found, incomplete strategy

% (8592)Memory used [KB]: 10618
% (8592)Time elapsed: 0.046 s
% (8592)------------------------------
% (8592)------------------------------
fof(f66,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f50,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f94,plain,
    ( spl6_1
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f86,f82,f46])).

fof(f82,plain,
    ( spl6_6
  <=> r2_hidden(k4_tarski(sK0,sK2(k11_relat_1(sK1,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f86,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl6_6 ),
    inference(resolution,[],[f83,f43])).

fof(f43,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,
    ( r2_hidden(k4_tarski(sK0,sK2(k11_relat_1(sK1,sK0))),sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f84,plain,
    ( spl6_6
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f80,f65,f56,f49,f82])).

fof(f80,plain,
    ( r2_hidden(k4_tarski(sK0,sK2(k11_relat_1(sK1,sK0))),sK1)
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(trivial_inequality_removal,[],[f79])).

fof(f79,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | r2_hidden(k4_tarski(sK0,sK2(k11_relat_1(sK1,sK0))),sK1)
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f77,f66])).

fof(f77,plain,
    ( o_0_0_xboole_0 != k1_xboole_0
    | r2_hidden(k4_tarski(sK0,sK2(k11_relat_1(sK1,sK0))),sK1)
    | spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(superposition,[],[f53,f76])).

fof(f76,plain,
    ( ! [X0] :
        ( o_0_0_xboole_0 = k11_relat_1(sK1,X0)
        | r2_hidden(k4_tarski(X0,sK2(k11_relat_1(sK1,X0))),sK1) )
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(resolution,[],[f75,f70])).

fof(f70,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0),X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl6_5 ),
    inference(resolution,[],[f69,f34])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f3,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,X1)
        | r2_hidden(X0,X1)
        | o_0_0_xboole_0 = X1 )
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f68,f66])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f35,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f75,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k11_relat_1(sK1,X1))
        | r2_hidden(k4_tarski(X1,X0),sK1) )
    | ~ spl6_3 ),
    inference(resolution,[],[f42,f57])).

fof(f57,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f67,plain,
    ( spl6_5
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f63,f60,f65])).

fof(f63,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl6_4 ),
    inference(resolution,[],[f33,f61])).

fof(f61,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f62,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f32,f60])).

fof(f32,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f58,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f29,f56])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
      | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
      | r2_hidden(sK0,k1_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
        | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
      & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
        | r2_hidden(sK0,k1_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f54,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f30,f49,f46])).

fof(f30,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f31,f49,f46])).

fof(f31,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f19])).

%------------------------------------------------------------------------------
