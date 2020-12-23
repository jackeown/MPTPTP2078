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
% DateTime   : Thu Dec  3 12:43:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 175 expanded)
%              Number of leaves         :   23 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  247 ( 440 expanded)
%              Number of equality atoms :   27 (  47 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f721,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f306,f531,f618,f623,f663,f709,f720])).

fof(f720,plain,
    ( ~ spl6_8
    | spl6_18 ),
    inference(avatar_contradiction_clause,[],[f716])).

fof(f716,plain,
    ( $false
    | ~ spl6_8
    | spl6_18 ),
    inference(resolution,[],[f693,f638])).

fof(f638,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl6_8 ),
    inference(resolution,[],[f301,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f301,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl6_8
  <=> ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f693,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl6_18 ),
    inference(resolution,[],[f662,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f662,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f660])).

fof(f660,plain,
    ( spl6_18
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f709,plain,(
    spl6_17 ),
    inference(avatar_contradiction_clause,[],[f705])).

fof(f705,plain,
    ( $false
    | spl6_17 ),
    inference(resolution,[],[f690,f37])).

fof(f37,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f27])).

fof(f27,plain,
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

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f690,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl6_17 ),
    inference(resolution,[],[f658,f49])).

fof(f658,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f656])).

fof(f656,plain,
    ( spl6_17
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f663,plain,
    ( ~ spl6_17
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f141,f660,f656])).

fof(f141,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f56,f71])).

fof(f71,plain,(
    ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f49,f38])).

fof(f38,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f623,plain,
    ( spl6_9
    | ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f619])).

fof(f619,plain,
    ( $false
    | spl6_9
    | ~ spl6_11 ),
    inference(resolution,[],[f426,f405])).

fof(f405,plain,
    ( r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f404])).

fof(f404,plain,
    ( spl6_11
  <=> r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f426,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1)
    | spl6_9 ),
    inference(resolution,[],[f162,f314])).

fof(f314,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl6_9 ),
    inference(resolution,[],[f305,f49])).

fof(f305,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl6_9
  <=> r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
      | ~ r1_xboole_0(X2,X0) ) ),
    inference(superposition,[],[f70,f63])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f40,f42,f42])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f42])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f618,plain,
    ( spl6_11
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f613])).

fof(f613,plain,
    ( $false
    | spl6_11
    | ~ spl6_12 ),
    inference(resolution,[],[f423,f410])).

fof(f410,plain,
    ( r1_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f409])).

fof(f409,plain,
    ( spl6_12
  <=> r1_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f423,plain,
    ( ~ r1_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3))
    | spl6_11 ),
    inference(resolution,[],[f406,f49])).

fof(f406,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f404])).

fof(f531,plain,(
    spl6_12 ),
    inference(avatar_contradiction_clause,[],[f527])).

fof(f527,plain,
    ( $false
    | spl6_12 ),
    inference(resolution,[],[f517,f37])).

fof(f517,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl6_12 ),
    inference(resolution,[],[f512,f49])).

fof(f512,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl6_12 ),
    inference(resolution,[],[f511,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f47,f36])).

fof(f36,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f511,plain,
    ( r2_hidden(sK3,sK1)
    | spl6_12 ),
    inference(resolution,[],[f201,f411])).

fof(f411,plain,
    ( ~ r1_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f409])).

fof(f201,plain,(
    ! [X6,X5] :
      ( r1_xboole_0(X5,k2_enumset1(X6,X6,X6,X6))
      | r2_hidden(X6,X5) ) ),
    inference(trivial_inequality_removal,[],[f194])).

fof(f194,plain,(
    ! [X6,X5] :
      ( X5 != X5
      | r1_xboole_0(X5,k2_enumset1(X6,X6,X6,X6))
      | r2_hidden(X6,X5) ) ),
    inference(superposition,[],[f51,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f53,f61])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f306,plain,
    ( spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f298,f303,f300])).

fof(f298,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))
      | ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ) ),
    inference(resolution,[],[f116,f62])).

fof(f62,plain,(
    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f35,f42,f61])).

fof(f35,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f64,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f42])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f42])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:25:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.43  % (23680)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (23669)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (23668)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (23670)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (23678)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (23676)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (23679)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (23675)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (23677)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (23670)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f721,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f306,f531,f618,f623,f663,f709,f720])).
% 0.22/0.50  fof(f720,plain,(
% 0.22/0.50    ~spl6_8 | spl6_18),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f716])).
% 0.22/0.50  fof(f716,plain,(
% 0.22/0.50    $false | (~spl6_8 | spl6_18)),
% 0.22/0.50    inference(resolution,[],[f693,f638])).
% 0.22/0.50  fof(f638,plain,(
% 0.22/0.50    r1_xboole_0(sK0,sK1) | ~spl6_8),
% 0.22/0.50    inference(resolution,[],[f301,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f43,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(rectify,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.50  fof(f301,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | ~spl6_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f300])).
% 0.22/0.50  fof(f300,plain,(
% 0.22/0.50    spl6_8 <=> ! [X0] : ~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.50  fof(f693,plain,(
% 0.22/0.50    ~r1_xboole_0(sK0,sK1) | spl6_18),
% 0.22/0.50    inference(resolution,[],[f662,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.50  fof(f662,plain,(
% 0.22/0.50    ~r1_xboole_0(sK1,sK0) | spl6_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f660])).
% 0.22/0.50  fof(f660,plain,(
% 0.22/0.50    spl6_18 <=> r1_xboole_0(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.50  fof(f709,plain,(
% 0.22/0.50    spl6_17),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f705])).
% 0.22/0.50  fof(f705,plain,(
% 0.22/0.50    $false | spl6_17),
% 0.22/0.50    inference(resolution,[],[f690,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    r1_xboole_0(sK2,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.22/0.50    inference(flattening,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.22/0.50    inference(ennf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.22/0.50    inference(negated_conjecture,[],[f15])).
% 0.22/0.50  fof(f15,conjecture,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.22/0.50  fof(f690,plain,(
% 0.22/0.50    ~r1_xboole_0(sK2,sK1) | spl6_17),
% 0.22/0.50    inference(resolution,[],[f658,f49])).
% 0.22/0.50  fof(f658,plain,(
% 0.22/0.50    ~r1_xboole_0(sK1,sK2) | spl6_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f656])).
% 0.22/0.50  fof(f656,plain,(
% 0.22/0.50    spl6_17 <=> r1_xboole_0(sK1,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.50  fof(f663,plain,(
% 0.22/0.50    ~spl6_17 | ~spl6_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f141,f660,f656])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK1,sK2)),
% 0.22/0.50    inference(resolution,[],[f56,f71])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 0.22/0.50    inference(resolution,[],[f49,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.22/0.50  fof(f623,plain,(
% 0.22/0.50    spl6_9 | ~spl6_11),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f619])).
% 0.22/0.50  fof(f619,plain,(
% 0.22/0.50    $false | (spl6_9 | ~spl6_11)),
% 0.22/0.50    inference(resolution,[],[f426,f405])).
% 0.22/0.50  fof(f405,plain,(
% 0.22/0.50    r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1) | ~spl6_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f404])).
% 0.22/0.50  fof(f404,plain,(
% 0.22/0.50    spl6_11 <=> r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.50  fof(f426,plain,(
% 0.22/0.50    ~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1) | spl6_9),
% 0.22/0.50    inference(resolution,[],[f162,f314])).
% 0.22/0.50  fof(f314,plain,(
% 0.22/0.50    ~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl6_9),
% 0.22/0.50    inference(resolution,[],[f305,f49])).
% 0.22/0.50  fof(f305,plain,(
% 0.22/0.50    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) | spl6_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f303])).
% 0.22/0.50  fof(f303,plain,(
% 0.22/0.50    spl6_9 <=> r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X0))) | ~r1_xboole_0(X2,X0)) )),
% 0.22/0.50    inference(superposition,[],[f70,f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f40,f42,f42])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f59,f42])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).
% 0.22/0.50  fof(f618,plain,(
% 0.22/0.50    spl6_11 | ~spl6_12),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f613])).
% 0.22/0.50  fof(f613,plain,(
% 0.22/0.50    $false | (spl6_11 | ~spl6_12)),
% 0.22/0.50    inference(resolution,[],[f423,f410])).
% 0.22/0.50  fof(f410,plain,(
% 0.22/0.50    r1_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3)) | ~spl6_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f409])).
% 0.22/0.50  fof(f409,plain,(
% 0.22/0.50    spl6_12 <=> r1_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.50  fof(f423,plain,(
% 0.22/0.50    ~r1_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3)) | spl6_11),
% 0.22/0.50    inference(resolution,[],[f406,f49])).
% 0.22/0.50  fof(f406,plain,(
% 0.22/0.50    ~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK1) | spl6_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f404])).
% 0.22/0.50  fof(f531,plain,(
% 0.22/0.50    spl6_12),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f527])).
% 0.22/0.50  fof(f527,plain,(
% 0.22/0.50    $false | spl6_12),
% 0.22/0.50    inference(resolution,[],[f517,f37])).
% 0.22/0.50  fof(f517,plain,(
% 0.22/0.50    ~r1_xboole_0(sK2,sK1) | spl6_12),
% 0.22/0.50    inference(resolution,[],[f512,f49])).
% 0.22/0.50  fof(f512,plain,(
% 0.22/0.50    ~r1_xboole_0(sK1,sK2) | spl6_12),
% 0.22/0.50    inference(resolution,[],[f511,f100])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(X0,sK2)) )),
% 0.22/0.50    inference(resolution,[],[f47,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    r2_hidden(sK3,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(rectify,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.50  fof(f511,plain,(
% 0.22/0.50    r2_hidden(sK3,sK1) | spl6_12),
% 0.22/0.50    inference(resolution,[],[f201,f411])).
% 0.22/0.50  fof(f411,plain,(
% 0.22/0.50    ~r1_xboole_0(sK1,k2_enumset1(sK3,sK3,sK3,sK3)) | spl6_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f409])).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    ( ! [X6,X5] : (r1_xboole_0(X5,k2_enumset1(X6,X6,X6,X6)) | r2_hidden(X6,X5)) )),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f194])).
% 0.22/0.50  fof(f194,plain,(
% 0.22/0.50    ( ! [X6,X5] : (X5 != X5 | r1_xboole_0(X5,k2_enumset1(X6,X6,X6,X6)) | r2_hidden(X6,X5)) )),
% 0.22/0.50    inference(superposition,[],[f51,f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f53,f61])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f39,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f41,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,axiom,(
% 0.22/0.50    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(nnf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.50  fof(f306,plain,(
% 0.22/0.50    spl6_8 | ~spl6_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f298,f303,f300])).
% 0.22/0.50  fof(f298,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) | ~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) )),
% 0.22/0.50    inference(resolution,[],[f116,f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.22/0.50    inference(definition_unfolding,[],[f35,f42,f61])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.50    inference(superposition,[],[f64,f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f48,f42])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f44,f42])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (23670)------------------------------
% 0.22/0.50  % (23670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (23670)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (23670)Memory used [KB]: 6396
% 0.22/0.50  % (23670)Time elapsed: 0.082 s
% 0.22/0.50  % (23670)------------------------------
% 0.22/0.50  % (23670)------------------------------
% 0.22/0.50  % (23671)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.50  % (23665)Success in time 0.137 s
%------------------------------------------------------------------------------
