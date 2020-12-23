%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 275 expanded)
%              Number of leaves         :   24 (  90 expanded)
%              Depth                    :   18
%              Number of atoms          :  331 ( 990 expanded)
%              Number of equality atoms :   42 ( 147 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f301,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f100,f196,f215,f261,f269,f300])).

fof(f300,plain,
    ( spl5_5
    | spl5_9
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f297,f83,f213,f198])).

fof(f198,plain,
    ( spl5_5
  <=> ! [X4] : ~ r2_hidden(X4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f213,plain,
    ( spl5_9
  <=> ! [X0] :
        ( ~ v3_ordinal1(X0)
        | ~ r1_tarski(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f83,plain,
    ( spl5_1
  <=> ! [X0] :
        ( ~ v3_ordinal1(X0)
        | ~ r2_hidden(sK4(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f297,plain,
    ( ! [X0,X1] :
        ( ~ v3_ordinal1(X0)
        | ~ r1_tarski(sK0,X0)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f273,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK4(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK4(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f32])).

fof(f32,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK4(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK4(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f273,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(sK4(sK0),X2)
        | ~ v3_ordinal1(X1)
        | ~ r1_tarski(X2,X1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f84,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f84,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0),X0)
        | ~ v3_ordinal1(X0) )
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f269,plain,(
    ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | ~ spl5_9 ),
    inference(resolution,[],[f265,f34])).

fof(f34,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ! [X2] :
        ( ( ~ r1_ordinal1(X2,sK2(X2))
          & r2_hidden(sK2(X2),sK0)
          & v3_ordinal1(sK2(X2)) )
        | ~ r2_hidden(X2,sK0)
        | ~ v3_ordinal1(X2) )
    & k1_xboole_0 != sK0
    & r1_tarski(sK0,sK1)
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f26,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ? [X3] :
                ( ~ r1_ordinal1(X2,X3)
                & r2_hidden(X3,X0)
                & v3_ordinal1(X3) )
            | ~ r2_hidden(X2,X0)
            | ~ v3_ordinal1(X2) )
        & k1_xboole_0 != X0
        & r1_tarski(X0,X1)
        & v3_ordinal1(X1) )
   => ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,sK0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,sK0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != sK0
      & r1_tarski(sK0,sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2] :
      ( ? [X3] :
          ( ~ r1_ordinal1(X2,X3)
          & r2_hidden(X3,sK0)
          & v3_ordinal1(X3) )
     => ( ~ r1_ordinal1(X2,sK2(X2))
        & r2_hidden(sK2(X2),sK0)
        & v3_ordinal1(sK2(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,X0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,X0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v3_ordinal1(X1)
       => ~ ( ! [X2] :
                ( v3_ordinal1(X2)
               => ~ ( ! [X3] :
                        ( v3_ordinal1(X3)
                       => ( r2_hidden(X3,X0)
                         => r1_ordinal1(X2,X3) ) )
                    & r2_hidden(X2,X0) ) )
            & k1_xboole_0 != X0
            & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ~ ( ! [X2] :
              ( v3_ordinal1(X2)
             => ~ ( ! [X3] :
                      ( v3_ordinal1(X3)
                     => ( r2_hidden(X3,X0)
                       => r1_ordinal1(X2,X3) ) )
                  & r2_hidden(X2,X0) ) )
          & k1_xboole_0 != X0
          & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_ordinal1)).

fof(f265,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ spl5_9 ),
    inference(resolution,[],[f214,f35])).

fof(f35,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f214,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | ~ v3_ordinal1(X0) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f213])).

fof(f261,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | ~ spl5_5 ),
    inference(trivial_inequality_removal,[],[f259])).

fof(f259,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl5_5 ),
    inference(superposition,[],[f36,f224])).

fof(f224,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_5 ),
    inference(resolution,[],[f199,f121])).

fof(f121,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f109,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f109,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f108,f41])).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f108,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(X0,k1_xboole_0)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f64,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f61,f41])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0))) ),
    inference(definition_unfolding,[],[f40,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f45,f59])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f199,plain,
    ( ! [X4] : ~ r2_hidden(X4,sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f198])).

fof(f36,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f27])).

fof(f215,plain,
    ( spl5_5
    | spl5_9
    | spl5_3 ),
    inference(avatar_split_clause,[],[f118,f93,f213,f198])).

fof(f93,plain,
    ( spl5_3
  <=> v3_ordinal1(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( ~ v3_ordinal1(X0)
        | ~ r1_tarski(sK0,X0)
        | ~ r2_hidden(X1,sK0) )
    | spl5_3 ),
    inference(resolution,[],[f111,f51])).

fof(f111,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(sK4(sK0),X2)
        | ~ v3_ordinal1(X1)
        | ~ r1_tarski(X2,X1) )
    | spl5_3 ),
    inference(resolution,[],[f101,f48])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0),X0)
        | ~ v3_ordinal1(X0) )
    | spl5_3 ),
    inference(resolution,[],[f95,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f95,plain,
    ( ~ v3_ordinal1(sK4(sK0))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f196,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl5_4 ),
    inference(trivial_inequality_removal,[],[f194])).

fof(f194,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl5_4 ),
    inference(superposition,[],[f36,f154])).

fof(f154,plain,
    ( k1_xboole_0 = sK0
    | spl5_4 ),
    inference(resolution,[],[f121,f102])).

fof(f102,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | spl5_4 ),
    inference(resolution,[],[f99,f51])).

fof(f99,plain,
    ( ~ r2_hidden(sK4(sK0),sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_4
  <=> r2_hidden(sK4(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f100,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | spl5_2 ),
    inference(avatar_split_clause,[],[f90,f86,f97,f93])).

fof(f86,plain,
    ( spl5_2
  <=> r2_hidden(sK2(sK4(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f90,plain,
    ( ~ r2_hidden(sK4(sK0),sK0)
    | ~ v3_ordinal1(sK4(sK0))
    | spl5_2 ),
    inference(resolution,[],[f88,f38])).

fof(f38,plain,(
    ! [X2] :
      ( r2_hidden(sK2(X2),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f88,plain,
    ( ~ r2_hidden(sK2(sK4(sK0)),sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f89,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f81,f86,f83])).

fof(f81,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(sK4(sK0)),sK0)
      | ~ v3_ordinal1(X0)
      | ~ r2_hidden(sK4(sK0),X0) ) ),
    inference(condensation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(sK4(sK0)),sK0)
      | ~ v3_ordinal1(X0)
      | ~ r2_hidden(sK4(sK0),X0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f78,f51])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0),sK0)
      | ~ r2_hidden(sK2(sK4(X0)),X0)
      | ~ v3_ordinal1(X1)
      | ~ r2_hidden(sK4(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0),X1)
      | ~ r2_hidden(sK2(sK4(X0)),X0)
      | ~ v3_ordinal1(X1)
      | ~ r2_hidden(sK4(X0),sK0)
      | ~ v3_ordinal1(X1) ) ),
    inference(condensation,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(sK4(X0)),X0)
      | ~ r2_hidden(sK4(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ r2_hidden(sK4(X0),sK0)
      | ~ r2_hidden(sK4(X0),X2)
      | ~ v3_ordinal1(X2) ) ),
    inference(resolution,[],[f75,f46])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(sK4(X0))
      | ~ r2_hidden(sK2(sK4(X0)),X0)
      | ~ r2_hidden(sK4(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ r2_hidden(sK4(X0),sK0) ) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0),sK0)
      | ~ r2_hidden(sK2(sK4(X0)),X0)
      | ~ r2_hidden(sK4(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ r2_hidden(sK4(X0),sK0)
      | ~ v3_ordinal1(sK4(X0)) ) ),
    inference(resolution,[],[f72,f37])).

fof(f37,plain,(
    ! [X2] :
      ( v3_ordinal1(sK2(X2))
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(sK2(sK4(X0)))
      | ~ r2_hidden(sK4(X0),sK0)
      | ~ r2_hidden(sK2(sK4(X0)),X0)
      | ~ r2_hidden(sK4(X0),X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f71,f46])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK4(X0))
      | ~ v3_ordinal1(sK2(sK4(X0)))
      | ~ r2_hidden(sK4(X0),sK0)
      | ~ r2_hidden(sK2(sK4(X0)),X0) ) ),
    inference(resolution,[],[f70,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK4(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(condensation,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK4(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | ~ v3_ordinal1(sK2(X0))
      | ~ v3_ordinal1(X0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | ~ v3_ordinal1(sK2(X0))
      | ~ v3_ordinal1(X0)
      | ~ r2_hidden(X0,sK0)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f42,f39])).

fof(f39,plain,(
    ! [X2] :
      ( ~ r1_ordinal1(X2,sK2(X2))
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:13:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.49  % (28785)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (28789)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.50  % (28793)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.50  % (28781)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (28781)Refutation not found, incomplete strategy% (28781)------------------------------
% 0.21/0.50  % (28781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28785)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f301,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f89,f100,f196,f215,f261,f269,f300])).
% 0.21/0.50  fof(f300,plain,(
% 0.21/0.50    spl5_5 | spl5_9 | ~spl5_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f297,f83,f213,f198])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    spl5_5 <=> ! [X4] : ~r2_hidden(X4,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    spl5_9 <=> ! [X0] : (~v3_ordinal1(X0) | ~r1_tarski(sK0,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    spl5_1 <=> ! [X0] : (~v3_ordinal1(X0) | ~r2_hidden(sK4(sK0),X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.50  fof(f297,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~r1_tarski(sK0,X0) | ~r2_hidden(X1,sK0)) ) | ~spl5_1),
% 0.21/0.50    inference(resolution,[],[f273,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK4(X1),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK4(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK4(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK4(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK4(X1),X1)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r2_hidden(sK4(sK0),X2) | ~v3_ordinal1(X1) | ~r1_tarski(X2,X1)) ) | ~spl5_1),
% 0.21/0.50    inference(resolution,[],[f84,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(rectify,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK4(sK0),X0) | ~v3_ordinal1(X0)) ) | ~spl5_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f83])).
% 0.21/0.51  fof(f269,plain,(
% 0.21/0.51    ~spl5_9),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f267])).
% 0.21/0.51  fof(f267,plain,(
% 0.21/0.51    $false | ~spl5_9),
% 0.21/0.51    inference(resolution,[],[f265,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    v3_ordinal1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X2] : ((~r1_ordinal1(X2,sK2(X2)) & r2_hidden(sK2(X2),sK0) & v3_ordinal1(sK2(X2))) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) & k1_xboole_0 != sK0 & r1_tarski(sK0,sK1) & v3_ordinal1(sK1)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f26,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ? [X0,X1] : (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,X0) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1) & v3_ordinal1(X1)) => (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,sK0) & v3_ordinal1(X3)) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) & k1_xboole_0 != sK0 & r1_tarski(sK0,sK1) & v3_ordinal1(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,sK0) & v3_ordinal1(X3)) => (~r1_ordinal1(X2,sK2(X2)) & r2_hidden(sK2(X2),sK0) & v3_ordinal1(sK2(X2))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0,X1] : (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,X0) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1) & v3_ordinal1(X1))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0,X1] : ((! [X2] : ((? [X3] : ((~r1_ordinal1(X2,X3) & r2_hidden(X3,X0)) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0)) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1)) & v3_ordinal1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : (v3_ordinal1(X1) => ~(! [X2] : (v3_ordinal1(X2) => ~(! [X3] : (v3_ordinal1(X3) => (r2_hidden(X3,X0) => r1_ordinal1(X2,X3))) & r2_hidden(X2,X0))) & k1_xboole_0 != X0 & r1_tarski(X0,X1)))),
% 0.21/0.51    inference(negated_conjecture,[],[f14])).
% 0.21/0.51  fof(f14,conjecture,(
% 0.21/0.51    ! [X0,X1] : (v3_ordinal1(X1) => ~(! [X2] : (v3_ordinal1(X2) => ~(! [X3] : (v3_ordinal1(X3) => (r2_hidden(X3,X0) => r1_ordinal1(X2,X3))) & r2_hidden(X2,X0))) & k1_xboole_0 != X0 & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_ordinal1)).
% 0.21/0.51  fof(f265,plain,(
% 0.21/0.51    ~v3_ordinal1(sK1) | ~spl5_9),
% 0.21/0.51    inference(resolution,[],[f214,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    r1_tarski(sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f214,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(sK0,X0) | ~v3_ordinal1(X0)) ) | ~spl5_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f213])).
% 0.21/0.51  fof(f261,plain,(
% 0.21/0.51    ~spl5_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f260])).
% 0.21/0.51  fof(f260,plain,(
% 0.21/0.51    $false | ~spl5_5),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f259])).
% 0.21/0.51  fof(f259,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | ~spl5_5),
% 0.21/0.51    inference(superposition,[],[f36,f224])).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | ~spl5_5),
% 0.21/0.51    inference(resolution,[],[f199,f121])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK3(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(resolution,[],[f109,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(forward_demodulation,[],[f108,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k1_xboole_0) | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(superposition,[],[f64,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f47,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f43,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f44,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f53,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f54,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)))) )),
% 0.21/0.51    inference(backward_demodulation,[],[f61,f41])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f40,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f45,f59])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    ( ! [X4] : (~r2_hidden(X4,sK0)) ) | ~spl5_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f198])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    k1_xboole_0 != sK0),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    spl5_5 | spl5_9 | spl5_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f118,f93,f213,f198])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    spl5_3 <=> v3_ordinal1(sK4(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~r1_tarski(sK0,X0) | ~r2_hidden(X1,sK0)) ) | spl5_3),
% 0.21/0.51    inference(resolution,[],[f111,f51])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~r2_hidden(sK4(sK0),X2) | ~v3_ordinal1(X1) | ~r1_tarski(X2,X1)) ) | spl5_3),
% 0.21/0.51    inference(resolution,[],[f101,f48])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK4(sK0),X0) | ~v3_ordinal1(X0)) ) | spl5_3),
% 0.21/0.51    inference(resolution,[],[f95,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ~v3_ordinal1(sK4(sK0)) | spl5_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f93])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    spl5_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f195])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    $false | spl5_4),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f194])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | spl5_4),
% 0.21/0.51    inference(superposition,[],[f36,f154])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | spl5_4),
% 0.21/0.51    inference(resolution,[],[f121,f102])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | spl5_4),
% 0.21/0.51    inference(resolution,[],[f99,f51])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK0),sK0) | spl5_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f97])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    spl5_4 <=> r2_hidden(sK4(sK0),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ~spl5_3 | ~spl5_4 | spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f90,f86,f97,f93])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl5_2 <=> r2_hidden(sK2(sK4(sK0)),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK0),sK0) | ~v3_ordinal1(sK4(sK0)) | spl5_2),
% 0.21/0.51    inference(resolution,[],[f88,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X2] : (r2_hidden(sK2(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ~r2_hidden(sK2(sK4(sK0)),sK0) | spl5_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f86])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    spl5_1 | ~spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f81,f86,f83])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK2(sK4(sK0)),sK0) | ~v3_ordinal1(X0) | ~r2_hidden(sK4(sK0),X0)) )),
% 0.21/0.51    inference(condensation,[],[f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK2(sK4(sK0)),sK0) | ~v3_ordinal1(X0) | ~r2_hidden(sK4(sK0),X0) | ~r2_hidden(X1,sK0)) )),
% 0.21/0.51    inference(resolution,[],[f78,f51])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK4(X0),sK0) | ~r2_hidden(sK2(sK4(X0)),X0) | ~v3_ordinal1(X1) | ~r2_hidden(sK4(X0),X1)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK4(X0),X1) | ~r2_hidden(sK2(sK4(X0)),X0) | ~v3_ordinal1(X1) | ~r2_hidden(sK4(X0),sK0) | ~v3_ordinal1(X1)) )),
% 0.21/0.51    inference(condensation,[],[f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(sK2(sK4(X0)),X0) | ~r2_hidden(sK4(X0),X1) | ~v3_ordinal1(X1) | ~r2_hidden(sK4(X0),sK0) | ~r2_hidden(sK4(X0),X2) | ~v3_ordinal1(X2)) )),
% 0.21/0.51    inference(resolution,[],[f75,f46])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v3_ordinal1(sK4(X0)) | ~r2_hidden(sK2(sK4(X0)),X0) | ~r2_hidden(sK4(X0),X1) | ~v3_ordinal1(X1) | ~r2_hidden(sK4(X0),sK0)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK4(X0),sK0) | ~r2_hidden(sK2(sK4(X0)),X0) | ~r2_hidden(sK4(X0),X1) | ~v3_ordinal1(X1) | ~r2_hidden(sK4(X0),sK0) | ~v3_ordinal1(sK4(X0))) )),
% 0.21/0.51    inference(resolution,[],[f72,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X2] : (v3_ordinal1(sK2(X2)) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v3_ordinal1(sK2(sK4(X0))) | ~r2_hidden(sK4(X0),sK0) | ~r2_hidden(sK2(sK4(X0)),X0) | ~r2_hidden(sK4(X0),X1) | ~v3_ordinal1(X1)) )),
% 0.21/0.51    inference(resolution,[],[f71,f46])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0] : (~v3_ordinal1(sK4(X0)) | ~v3_ordinal1(sK2(sK4(X0))) | ~r2_hidden(sK4(X0),sK0) | ~r2_hidden(sK2(sK4(X0)),X0)) )),
% 0.21/0.51    inference(resolution,[],[f70,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,sK4(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(condensation,[],[f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK4(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK2(X0),X0) | ~v3_ordinal1(sK2(X0)) | ~v3_ordinal1(X0) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK2(X0),X0) | ~v3_ordinal1(sK2(X0)) | ~v3_ordinal1(X0) | ~r2_hidden(X0,sK0) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(resolution,[],[f42,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X2] : (~r1_ordinal1(X2,sK2(X2)) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (28785)------------------------------
% 0.21/0.51  % (28785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28785)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (28785)Memory used [KB]: 6268
% 0.21/0.51  % (28785)Time elapsed: 0.101 s
% 0.21/0.51  % (28785)------------------------------
% 0.21/0.51  % (28785)------------------------------
% 0.21/0.51  % (28772)Success in time 0.154 s
%------------------------------------------------------------------------------
