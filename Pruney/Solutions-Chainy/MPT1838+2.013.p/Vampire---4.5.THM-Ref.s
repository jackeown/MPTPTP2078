%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:56 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 294 expanded)
%              Number of leaves         :   24 (  91 expanded)
%              Depth                    :   19
%              Number of atoms          :  336 (1061 expanded)
%              Number of equality atoms :  114 ( 291 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f610,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f515,f566,f569,f606])).

fof(f606,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f605])).

fof(f605,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f591,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f591,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f144,f481])).

fof(f481,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f479])).

fof(f479,plain,
    ( spl5_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f144,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f140,f126])).

fof(f126,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f123,f87])).

fof(f87,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f71,f48])).

fof(f71,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f49,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f49,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f123,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[],[f73,f48])).

fof(f73,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f57,f58,f59])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f140,plain,(
    ! [X0] : k1_xboole_0 != k4_xboole_0(sK0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) ),
    inference(resolution,[],[f116,f42])).

fof(f42,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK0 != sK1
    & r1_tarski(sK0,sK1)
    & v1_zfmisc_1(sK1)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & r1_tarski(sK0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( sK0 != X1
        & r1_tarski(sK0,X1)
        & v1_zfmisc_1(X1)
        & ~ v1_xboole_0(X1) )
   => ( sK0 != sK1
      & r1_tarski(sK0,sK1)
      & v1_zfmisc_1(sK1)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f116,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | k1_xboole_0 != k4_xboole_0(X0,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) ) ),
    inference(resolution,[],[f114,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f108,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f58])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f108,plain,(
    ! [X0,X1] : v1_xboole_0(k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,k1_xboole_0))))) ),
    inference(resolution,[],[f93,f55])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f93,plain,(
    ! [X2,X3,X1] : ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X2,k1_setfam_1(k2_tarski(X3,k1_xboole_0))))) ),
    inference(resolution,[],[f91,f84])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f65,f58])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f91,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) ),
    inference(resolution,[],[f90,f47])).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(resolution,[],[f84,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f569,plain,
    ( spl5_1
    | spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f568,f483,f487,f479])).

fof(f487,plain,
    ( spl5_3
  <=> ! [X2] : sK1 != k2_tarski(X2,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f483,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f568,plain,
    ( ! [X0] :
        ( k2_tarski(X0,X0) != sK1
        | k1_xboole_0 = sK0 )
    | spl5_2 ),
    inference(subsumption_resolution,[],[f567,f484])).

fof(f484,plain,
    ( k1_xboole_0 != sK1
    | spl5_2 ),
    inference(avatar_component_clause,[],[f483])).

fof(f567,plain,(
    ! [X0] :
      ( k2_tarski(X0,X0) != sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f542,f46])).

fof(f46,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f542,plain,(
    ! [X0] :
      ( k2_tarski(X0,X0) != sK1
      | k1_xboole_0 = sK0
      | sK0 = sK1
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f82,f159])).

fof(f159,plain,(
    sK1 = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f153,f87])).

fof(f153,plain,(
    k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f72,f88])).

fof(f88,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f63,f45])).

fof(f45,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f72,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f56,f59,f59])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X0) != k5_xboole_0(X1,k4_xboole_0(X2,X1))
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_xboole_0 = X2 ) ),
    inference(definition_unfolding,[],[f70,f50,f59])).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f566,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f565])).

fof(f565,plain,
    ( $false
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f564,f43])).

fof(f43,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f564,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f563,f44])).

fof(f44,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f563,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | ~ spl5_3 ),
    inference(trivial_inequality_removal,[],[f562])).

fof(f562,plain,
    ( sK1 != sK1
    | ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | ~ spl5_3 ),
    inference(superposition,[],[f546,f52])).

fof(f52,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK2(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f546,plain,
    ( sK1 != k6_domain_1(sK1,sK2(sK1))
    | ~ spl5_3 ),
    inference(superposition,[],[f488,f469])).

fof(f469,plain,(
    k6_domain_1(sK1,sK2(sK1)) = k2_tarski(sK2(sK1),sK2(sK1)) ),
    inference(subsumption_resolution,[],[f468,f43])).

fof(f468,plain,
    ( v1_xboole_0(sK1)
    | k6_domain_1(sK1,sK2(sK1)) = k2_tarski(sK2(sK1),sK2(sK1)) ),
    inference(resolution,[],[f164,f44])).

fof(f164,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,sK2(X0)) = k2_tarski(sK2(X0),sK2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK2(X0)) = k2_tarski(sK2(X0),sK2(X0))
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f75,f51])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f61,f50])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f488,plain,
    ( ! [X2] : sK1 != k2_tarski(X2,X2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f487])).

fof(f515,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f514])).

fof(f514,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f498,f48])).

fof(f498,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f146,f485])).

fof(f485,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f483])).

fof(f146,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f141,f126])).

fof(f141,plain,(
    ! [X1] : k1_xboole_0 != k4_xboole_0(sK1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) ),
    inference(resolution,[],[f116,f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (14024)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.49  % (14038)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (14038)Refutation not found, incomplete strategy% (14038)------------------------------
% 0.20/0.50  % (14038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (14038)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (14038)Memory used [KB]: 10746
% 0.20/0.50  % (14038)Time elapsed: 0.030 s
% 0.20/0.50  % (14038)------------------------------
% 0.20/0.50  % (14038)------------------------------
% 0.20/0.50  % (14030)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (14019)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (14026)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (14044)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (14031)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (14020)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (14017)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.33/0.53  % (14021)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.33/0.54  % (14026)Refutation not found, incomplete strategy% (14026)------------------------------
% 1.33/0.54  % (14026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (14026)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (14026)Memory used [KB]: 10618
% 1.33/0.54  % (14026)Time elapsed: 0.125 s
% 1.33/0.54  % (14026)------------------------------
% 1.33/0.54  % (14026)------------------------------
% 1.33/0.54  % (14018)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.33/0.54  % (14042)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.33/0.54  % (14043)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.33/0.54  % (14029)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.33/0.54  % (14035)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.33/0.54  % (14034)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.33/0.54  % (14036)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.33/0.54  % (14036)Refutation not found, incomplete strategy% (14036)------------------------------
% 1.33/0.54  % (14036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (14036)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (14036)Memory used [KB]: 10746
% 1.33/0.54  % (14028)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.55  % (14015)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.33/0.55  % (14027)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.33/0.55  % (14025)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.49/0.55  % (14027)Refutation not found, incomplete strategy% (14027)------------------------------
% 1.49/0.55  % (14027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (14027)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (14027)Memory used [KB]: 10618
% 1.49/0.55  % (14027)Time elapsed: 0.138 s
% 1.49/0.55  % (14027)------------------------------
% 1.49/0.55  % (14027)------------------------------
% 1.49/0.55  % (14025)Refutation not found, incomplete strategy% (14025)------------------------------
% 1.49/0.55  % (14025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (14025)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (14025)Memory used [KB]: 10746
% 1.49/0.55  % (14025)Time elapsed: 0.138 s
% 1.49/0.55  % (14025)------------------------------
% 1.49/0.55  % (14025)------------------------------
% 1.49/0.55  % (14041)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.49/0.55  % (14023)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.49/0.55  % (14045)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.49/0.55  % (14019)Refutation found. Thanks to Tanya!
% 1.49/0.55  % SZS status Theorem for theBenchmark
% 1.49/0.55  % SZS output start Proof for theBenchmark
% 1.49/0.55  fof(f610,plain,(
% 1.49/0.55    $false),
% 1.49/0.55    inference(avatar_sat_refutation,[],[f515,f566,f569,f606])).
% 1.49/0.55  fof(f606,plain,(
% 1.49/0.55    ~spl5_1),
% 1.49/0.55    inference(avatar_contradiction_clause,[],[f605])).
% 1.49/0.55  fof(f605,plain,(
% 1.49/0.55    $false | ~spl5_1),
% 1.49/0.55    inference(subsumption_resolution,[],[f591,f48])).
% 1.49/0.55  fof(f48,plain,(
% 1.49/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f9])).
% 1.49/0.55  fof(f9,axiom,(
% 1.49/0.55    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.49/0.55  fof(f591,plain,(
% 1.49/0.55    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_1),
% 1.49/0.55    inference(backward_demodulation,[],[f144,f481])).
% 1.49/0.55  fof(f481,plain,(
% 1.49/0.55    k1_xboole_0 = sK0 | ~spl5_1),
% 1.49/0.55    inference(avatar_component_clause,[],[f479])).
% 1.49/0.55  fof(f479,plain,(
% 1.49/0.55    spl5_1 <=> k1_xboole_0 = sK0),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.49/0.55  fof(f144,plain,(
% 1.49/0.55    k1_xboole_0 != k4_xboole_0(sK0,k1_xboole_0)),
% 1.49/0.55    inference(superposition,[],[f140,f126])).
% 1.49/0.55  fof(f126,plain,(
% 1.49/0.55    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 1.49/0.55    inference(forward_demodulation,[],[f123,f87])).
% 1.49/0.55  fof(f87,plain,(
% 1.49/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.49/0.55    inference(forward_demodulation,[],[f71,f48])).
% 1.49/0.55  fof(f71,plain,(
% 1.49/0.55    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 1.49/0.55    inference(definition_unfolding,[],[f49,f59])).
% 1.49/0.55  fof(f59,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f10])).
% 1.49/0.55  fof(f10,axiom,(
% 1.49/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.49/0.55  fof(f49,plain,(
% 1.49/0.55    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.49/0.55    inference(cnf_transformation,[],[f6])).
% 1.49/0.55  fof(f6,axiom,(
% 1.49/0.55    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.49/0.55  fof(f123,plain,(
% 1.49/0.55    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_xboole_0))) = X0) )),
% 1.49/0.55    inference(superposition,[],[f73,f48])).
% 1.49/0.55  fof(f73,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0) )),
% 1.49/0.55    inference(definition_unfolding,[],[f57,f58,f59])).
% 1.49/0.55  fof(f58,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f13])).
% 1.49/0.55  fof(f13,axiom,(
% 1.49/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.49/0.55  fof(f57,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.49/0.55    inference(cnf_transformation,[],[f7])).
% 1.49/0.55  fof(f7,axiom,(
% 1.49/0.55    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.49/0.55  fof(f140,plain,(
% 1.49/0.55    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(sK0,k1_setfam_1(k2_tarski(X0,k1_xboole_0)))) )),
% 1.49/0.55    inference(resolution,[],[f116,f42])).
% 1.49/0.55  fof(f42,plain,(
% 1.49/0.55    ~v1_xboole_0(sK0)),
% 1.49/0.55    inference(cnf_transformation,[],[f27])).
% 1.49/0.55  fof(f27,plain,(
% 1.49/0.55    (sK0 != sK1 & r1_tarski(sK0,sK1) & v1_zfmisc_1(sK1) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 1.49/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f26,f25])).
% 1.49/0.55  fof(f25,plain,(
% 1.49/0.55    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK0 != X1 & r1_tarski(sK0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f26,plain,(
% 1.49/0.55    ? [X1] : (sK0 != X1 & r1_tarski(sK0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK0 != sK1 & r1_tarski(sK0,sK1) & v1_zfmisc_1(sK1) & ~v1_xboole_0(sK1))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f19,plain,(
% 1.49/0.55    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.49/0.55    inference(flattening,[],[f18])).
% 1.49/0.55  fof(f18,plain,(
% 1.49/0.55    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 1.49/0.55    inference(ennf_transformation,[],[f17])).
% 1.49/0.55  fof(f17,negated_conjecture,(
% 1.49/0.55    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.49/0.55    inference(negated_conjecture,[],[f16])).
% 1.49/0.55  fof(f16,conjecture,(
% 1.49/0.55    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 1.49/0.55  fof(f116,plain,(
% 1.49/0.55    ( ! [X0,X1] : (v1_xboole_0(X0) | k1_xboole_0 != k4_xboole_0(X0,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))) )),
% 1.49/0.55    inference(resolution,[],[f114,f62])).
% 1.49/0.55  fof(f62,plain,(
% 1.49/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f36])).
% 1.49/0.55  fof(f36,plain,(
% 1.49/0.55    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.49/0.55    inference(nnf_transformation,[],[f5])).
% 1.49/0.55  fof(f5,axiom,(
% 1.49/0.55    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.49/0.55  fof(f114,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) | v1_xboole_0(X0)) )),
% 1.49/0.55    inference(superposition,[],[f108,f74])).
% 1.49/0.55  fof(f74,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.49/0.55    inference(definition_unfolding,[],[f60,f58])).
% 1.49/0.55  fof(f60,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f21])).
% 1.49/0.55  fof(f21,plain,(
% 1.49/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.49/0.55    inference(ennf_transformation,[],[f8])).
% 1.49/0.55  fof(f8,axiom,(
% 1.49/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.49/0.55  fof(f108,plain,(
% 1.49/0.55    ( ! [X0,X1] : (v1_xboole_0(k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))))) )),
% 1.49/0.55    inference(resolution,[],[f93,f55])).
% 1.49/0.55  fof(f55,plain,(
% 1.49/0.55    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f35])).
% 1.49/0.55  fof(f35,plain,(
% 1.49/0.55    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.49/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).
% 1.49/0.55  fof(f34,plain,(
% 1.49/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f33,plain,(
% 1.49/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.49/0.55    inference(rectify,[],[f32])).
% 1.49/0.55  fof(f32,plain,(
% 1.49/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.49/0.55    inference(nnf_transformation,[],[f2])).
% 1.49/0.55  fof(f2,axiom,(
% 1.49/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.49/0.55  fof(f93,plain,(
% 1.49/0.55    ( ! [X2,X3,X1] : (~r2_hidden(X1,k1_setfam_1(k2_tarski(X2,k1_setfam_1(k2_tarski(X3,k1_xboole_0)))))) )),
% 1.49/0.55    inference(resolution,[],[f91,f84])).
% 1.49/0.55  fof(f84,plain,(
% 1.49/0.55    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.49/0.55    inference(equality_resolution,[],[f80])).
% 1.49/0.55  fof(f80,plain,(
% 1.49/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 1.49/0.55    inference(definition_unfolding,[],[f65,f58])).
% 1.49/0.55  fof(f65,plain,(
% 1.49/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.49/0.55    inference(cnf_transformation,[],[f41])).
% 1.49/0.55  fof(f41,plain,(
% 1.49/0.55    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.49/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).
% 1.49/0.55  fof(f40,plain,(
% 1.49/0.55    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f39,plain,(
% 1.49/0.55    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.49/0.55    inference(rectify,[],[f38])).
% 1.49/0.55  fof(f38,plain,(
% 1.49/0.55    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.49/0.55    inference(flattening,[],[f37])).
% 1.49/0.55  fof(f37,plain,(
% 1.49/0.55    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.49/0.55    inference(nnf_transformation,[],[f3])).
% 1.49/0.55  fof(f3,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.49/0.55  fof(f91,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))) )),
% 1.49/0.55    inference(resolution,[],[f90,f47])).
% 1.49/0.55  fof(f47,plain,(
% 1.49/0.55    v1_xboole_0(k1_xboole_0)),
% 1.49/0.55    inference(cnf_transformation,[],[f4])).
% 1.49/0.55  fof(f4,axiom,(
% 1.49/0.55    v1_xboole_0(k1_xboole_0)),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.49/0.55  fof(f90,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 1.49/0.55    inference(resolution,[],[f84,f54])).
% 1.49/0.55  fof(f54,plain,(
% 1.49/0.55    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f35])).
% 1.49/0.55  fof(f569,plain,(
% 1.49/0.55    spl5_1 | spl5_3 | spl5_2),
% 1.49/0.55    inference(avatar_split_clause,[],[f568,f483,f487,f479])).
% 1.49/0.55  fof(f487,plain,(
% 1.49/0.55    spl5_3 <=> ! [X2] : sK1 != k2_tarski(X2,X2)),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.49/0.55  fof(f483,plain,(
% 1.49/0.55    spl5_2 <=> k1_xboole_0 = sK1),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.49/0.55  fof(f568,plain,(
% 1.49/0.55    ( ! [X0] : (k2_tarski(X0,X0) != sK1 | k1_xboole_0 = sK0) ) | spl5_2),
% 1.49/0.55    inference(subsumption_resolution,[],[f567,f484])).
% 1.49/0.55  fof(f484,plain,(
% 1.49/0.55    k1_xboole_0 != sK1 | spl5_2),
% 1.49/0.55    inference(avatar_component_clause,[],[f483])).
% 1.49/0.55  fof(f567,plain,(
% 1.49/0.55    ( ! [X0] : (k2_tarski(X0,X0) != sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1) )),
% 1.49/0.55    inference(subsumption_resolution,[],[f542,f46])).
% 1.49/0.55  fof(f46,plain,(
% 1.49/0.55    sK0 != sK1),
% 1.49/0.55    inference(cnf_transformation,[],[f27])).
% 1.49/0.55  fof(f542,plain,(
% 1.49/0.55    ( ! [X0] : (k2_tarski(X0,X0) != sK1 | k1_xboole_0 = sK0 | sK0 = sK1 | k1_xboole_0 = sK1) )),
% 1.49/0.55    inference(superposition,[],[f82,f159])).
% 1.49/0.55  fof(f159,plain,(
% 1.49/0.55    sK1 = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 1.49/0.55    inference(forward_demodulation,[],[f153,f87])).
% 1.49/0.55  fof(f153,plain,(
% 1.49/0.55    k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 1.49/0.55    inference(superposition,[],[f72,f88])).
% 1.49/0.55  fof(f88,plain,(
% 1.49/0.55    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.49/0.55    inference(resolution,[],[f63,f45])).
% 1.49/0.55  fof(f45,plain,(
% 1.49/0.55    r1_tarski(sK0,sK1)),
% 1.49/0.55    inference(cnf_transformation,[],[f27])).
% 1.49/0.55  fof(f63,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f36])).
% 1.49/0.55  fof(f72,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 1.49/0.55    inference(definition_unfolding,[],[f56,f59,f59])).
% 1.49/0.55  fof(f56,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f1])).
% 1.49/0.55  fof(f1,axiom,(
% 1.49/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.49/0.55  fof(f82,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (k2_tarski(X0,X0) != k5_xboole_0(X1,k4_xboole_0(X2,X1)) | k1_xboole_0 = X1 | X1 = X2 | k1_xboole_0 = X2) )),
% 1.49/0.55    inference(definition_unfolding,[],[f70,f50,f59])).
% 1.49/0.55  fof(f50,plain,(
% 1.49/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f11])).
% 1.49/0.55  fof(f11,axiom,(
% 1.49/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.49/0.55  fof(f70,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f24])).
% 1.49/0.55  fof(f24,plain,(
% 1.49/0.55    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 1.49/0.55    inference(ennf_transformation,[],[f12])).
% 1.49/0.55  fof(f12,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 1.49/0.55  fof(f566,plain,(
% 1.49/0.55    ~spl5_3),
% 1.49/0.55    inference(avatar_contradiction_clause,[],[f565])).
% 1.49/0.55  fof(f565,plain,(
% 1.49/0.55    $false | ~spl5_3),
% 1.49/0.55    inference(subsumption_resolution,[],[f564,f43])).
% 1.49/0.55  fof(f43,plain,(
% 1.49/0.55    ~v1_xboole_0(sK1)),
% 1.49/0.55    inference(cnf_transformation,[],[f27])).
% 1.49/0.55  fof(f564,plain,(
% 1.49/0.55    v1_xboole_0(sK1) | ~spl5_3),
% 1.49/0.55    inference(subsumption_resolution,[],[f563,f44])).
% 1.49/0.55  fof(f44,plain,(
% 1.49/0.55    v1_zfmisc_1(sK1)),
% 1.49/0.55    inference(cnf_transformation,[],[f27])).
% 1.49/0.55  fof(f563,plain,(
% 1.49/0.55    ~v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | ~spl5_3),
% 1.49/0.55    inference(trivial_inequality_removal,[],[f562])).
% 1.49/0.55  fof(f562,plain,(
% 1.49/0.55    sK1 != sK1 | ~v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | ~spl5_3),
% 1.49/0.55    inference(superposition,[],[f546,f52])).
% 1.49/0.55  fof(f52,plain,(
% 1.49/0.55    ( ! [X0] : (k6_domain_1(X0,sK2(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f31])).
% 1.49/0.55  fof(f31,plain,(
% 1.49/0.55    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.49/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 1.49/0.55  fof(f30,plain,(
% 1.49/0.55    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f29,plain,(
% 1.49/0.55    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.49/0.55    inference(rectify,[],[f28])).
% 1.49/0.55  fof(f28,plain,(
% 1.49/0.55    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.49/0.55    inference(nnf_transformation,[],[f20])).
% 1.49/0.55  fof(f20,plain,(
% 1.49/0.55    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 1.49/0.55    inference(ennf_transformation,[],[f15])).
% 1.49/0.55  fof(f15,axiom,(
% 1.49/0.55    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 1.49/0.55  fof(f546,plain,(
% 1.49/0.55    sK1 != k6_domain_1(sK1,sK2(sK1)) | ~spl5_3),
% 1.49/0.55    inference(superposition,[],[f488,f469])).
% 1.49/0.55  fof(f469,plain,(
% 1.49/0.55    k6_domain_1(sK1,sK2(sK1)) = k2_tarski(sK2(sK1),sK2(sK1))),
% 1.49/0.56    inference(subsumption_resolution,[],[f468,f43])).
% 1.49/0.56  fof(f468,plain,(
% 1.49/0.56    v1_xboole_0(sK1) | k6_domain_1(sK1,sK2(sK1)) = k2_tarski(sK2(sK1),sK2(sK1))),
% 1.49/0.56    inference(resolution,[],[f164,f44])).
% 1.49/0.56  fof(f164,plain,(
% 1.49/0.56    ( ! [X0] : (~v1_zfmisc_1(X0) | v1_xboole_0(X0) | k6_domain_1(X0,sK2(X0)) = k2_tarski(sK2(X0),sK2(X0))) )),
% 1.49/0.56    inference(duplicate_literal_removal,[],[f163])).
% 1.49/0.56  fof(f163,plain,(
% 1.49/0.56    ( ! [X0] : (k6_domain_1(X0,sK2(X0)) = k2_tarski(sK2(X0),sK2(X0)) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 1.49/0.56    inference(resolution,[],[f75,f51])).
% 1.49/0.56  fof(f51,plain,(
% 1.49/0.56    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f31])).
% 1.49/0.56  fof(f75,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 1.49/0.56    inference(definition_unfolding,[],[f61,f50])).
% 1.49/0.56  fof(f61,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f23])).
% 1.49/0.56  fof(f23,plain,(
% 1.49/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.49/0.56    inference(flattening,[],[f22])).
% 1.49/0.56  fof(f22,plain,(
% 1.49/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.49/0.56    inference(ennf_transformation,[],[f14])).
% 1.49/0.56  fof(f14,axiom,(
% 1.49/0.56    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.49/0.56  fof(f488,plain,(
% 1.49/0.56    ( ! [X2] : (sK1 != k2_tarski(X2,X2)) ) | ~spl5_3),
% 1.49/0.56    inference(avatar_component_clause,[],[f487])).
% 1.49/0.56  fof(f515,plain,(
% 1.49/0.56    ~spl5_2),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f514])).
% 1.49/0.56  fof(f514,plain,(
% 1.49/0.56    $false | ~spl5_2),
% 1.49/0.56    inference(subsumption_resolution,[],[f498,f48])).
% 1.49/0.56  fof(f498,plain,(
% 1.49/0.56    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_2),
% 1.49/0.56    inference(backward_demodulation,[],[f146,f485])).
% 1.49/0.56  fof(f485,plain,(
% 1.49/0.56    k1_xboole_0 = sK1 | ~spl5_2),
% 1.49/0.56    inference(avatar_component_clause,[],[f483])).
% 1.49/0.56  fof(f146,plain,(
% 1.49/0.56    k1_xboole_0 != k4_xboole_0(sK1,k1_xboole_0)),
% 1.49/0.56    inference(superposition,[],[f141,f126])).
% 1.49/0.56  fof(f141,plain,(
% 1.49/0.56    ( ! [X1] : (k1_xboole_0 != k4_xboole_0(sK1,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))) )),
% 1.49/0.56    inference(resolution,[],[f116,f43])).
% 1.49/0.56  % SZS output end Proof for theBenchmark
% 1.49/0.56  % (14019)------------------------------
% 1.49/0.56  % (14019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (14019)Termination reason: Refutation
% 1.49/0.56  
% 1.49/0.56  % (14019)Memory used [KB]: 11001
% 1.49/0.56  % (14019)Time elapsed: 0.118 s
% 1.49/0.56  % (14019)------------------------------
% 1.49/0.56  % (14019)------------------------------
% 1.49/0.56  % (14012)Success in time 0.197 s
%------------------------------------------------------------------------------
