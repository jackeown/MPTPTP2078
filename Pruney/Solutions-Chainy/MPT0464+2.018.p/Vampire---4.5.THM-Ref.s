%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:27 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 864 expanded)
%              Number of leaves         :   42 ( 291 expanded)
%              Depth                    :   21
%              Number of atoms          :  553 (1484 expanded)
%              Number of equality atoms :  184 ( 755 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f649,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f151,f155,f159,f163,f167,f239,f249,f254,f263,f269,f543,f546,f621])).

fof(f621,plain,
    ( ~ spl6_5
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f620])).

fof(f620,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f289,f619])).

fof(f619,plain,
    ( ! [X5] : ~ r1_tarski(k1_xboole_0,X5)
    | ~ spl6_5
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f566,f618])).

fof(f618,plain,
    ( ! [X7] : ~ r2_hidden(sK2,X7)
    | ~ spl6_5
    | ~ spl6_13 ),
    inference(trivial_inequality_removal,[],[f617])).

fof(f617,plain,
    ( ! [X7] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ r2_hidden(sK2,X7) )
    | ~ spl6_5
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f616,f285])).

fof(f285,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl6_5 ),
    inference(resolution,[],[f284,f166])).

fof(f166,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl6_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f284,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | k5_xboole_0(X1,X1) = X0 ) ),
    inference(forward_demodulation,[],[f282,f210])).

fof(f210,plain,(
    ! [X5] : k5_xboole_0(X5,X5) = k1_setfam_1(k4_enumset1(k5_xboole_0(X5,X5),k5_xboole_0(X5,X5),k5_xboole_0(X5,X5),k5_xboole_0(X5,X5),k5_xboole_0(X5,X5),X5)) ),
    inference(resolution,[],[f117,f196])).

fof(f196,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f113,f111])).

fof(f111,plain,(
    ! [X0] : k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f69,f108])).

fof(f108,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f73,f107])).

fof(f107,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f74,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f83,f105])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f91,f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f91,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f83,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f74,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f69,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f113,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f71,f109])).

fof(f109,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f75,f108])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f78,f108])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f282,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | k1_setfam_1(k4_enumset1(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),X1)) = X0 ) ),
    inference(resolution,[],[f206,f174])).

fof(f174,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK3(X2),X2)
      | ~ v1_xboole_0(X1)
      | X1 = X2 ) ),
    inference(resolution,[],[f82,f68])).

fof(f68,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f206,plain,(
    ! [X4,X3] : ~ r2_hidden(X3,k1_setfam_1(k4_enumset1(k5_xboole_0(X4,X4),k5_xboole_0(X4,X4),k5_xboole_0(X4,X4),k5_xboole_0(X4,X4),k5_xboole_0(X4,X4),X4))) ),
    inference(resolution,[],[f115,f193])).

fof(f193,plain,(
    ! [X0] : r1_xboole_0(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f112,f111])).

fof(f112,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1) ),
    inference(definition_unfolding,[],[f70,f109])).

fof(f70,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f77,f108])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f616,plain,
    ( ! [X7] :
        ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
        | ~ r2_hidden(sK2,X7) )
    | ~ spl6_5
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f568,f297])).

fof(f297,plain,
    ( ! [X0] : k1_xboole_0 = k1_setfam_1(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))
    | ~ spl6_5 ),
    inference(resolution,[],[f289,f117])).

fof(f568,plain,
    ( ! [X7] :
        ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_setfam_1(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X7)))
        | ~ r2_hidden(sK2,X7) )
    | ~ spl6_13 ),
    inference(superposition,[],[f123,f539])).

fof(f539,plain,
    ( k1_xboole_0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f538])).

fof(f538,plain,
    ( spl6_13
  <=> k1_xboole_0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( k4_enumset1(X0,X0,X0,X0,X0,X1) != k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k1_setfam_1(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),X2)))
      | ~ r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f89,f107,f109,f107])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f566,plain,
    ( ! [X5] :
        ( ~ r1_tarski(k1_xboole_0,X5)
        | r2_hidden(sK2,X5) )
    | ~ spl6_13 ),
    inference(superposition,[],[f120,f539])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f86,f107])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f289,plain,
    ( ! [X1] : r1_tarski(k1_xboole_0,X1)
    | ~ spl6_5 ),
    inference(superposition,[],[f196,f285])).

fof(f546,plain,(
    spl6_14 ),
    inference(avatar_contradiction_clause,[],[f545])).

fof(f545,plain,
    ( $false
    | spl6_14 ),
    inference(resolution,[],[f542,f138])).

fof(f138,plain,(
    ! [X2,X0,X7,X3,X1] : r2_hidden(X7,k4_enumset1(X0,X0,X1,X2,X3,X7)) ),
    inference(equality_resolution,[],[f137])).

fof(f137,plain,(
    ! [X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | k4_enumset1(X0,X0,X1,X2,X3,X7) != X5 ) ),
    inference(equality_resolution,[],[f131])).

fof(f131,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X4 != X7
      | k4_enumset1(X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f98,f92])).

fof(f98,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X4 != X7
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ( ( ( sK5(X0,X1,X2,X3,X4,X5) != X4
              & sK5(X0,X1,X2,X3,X4,X5) != X3
              & sK5(X0,X1,X2,X3,X4,X5) != X2
              & sK5(X0,X1,X2,X3,X4,X5) != X1
              & sK5(X0,X1,X2,X3,X4,X5) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5),X5) )
          & ( sK5(X0,X1,X2,X3,X4,X5) = X4
            | sK5(X0,X1,X2,X3,X4,X5) = X3
            | sK5(X0,X1,X2,X3,X4,X5) = X2
            | sK5(X0,X1,X2,X3,X4,X5) = X1
            | sK5(X0,X1,X2,X3,X4,X5) = X0
            | r2_hidden(sK5(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f57,f58])).

fof(f58,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 )
            | ~ r2_hidden(X6,X5) )
          & ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6
            | r2_hidden(X6,X5) ) )
     => ( ( ( sK5(X0,X1,X2,X3,X4,X5) != X4
            & sK5(X0,X1,X2,X3,X4,X5) != X3
            & sK5(X0,X1,X2,X3,X4,X5) != X2
            & sK5(X0,X1,X2,X3,X4,X5) != X1
            & sK5(X0,X1,X2,X3,X4,X5) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5),X5) )
        & ( sK5(X0,X1,X2,X3,X4,X5) = X4
          | sK5(X0,X1,X2,X3,X4,X5) = X3
          | sK5(X0,X1,X2,X3,X4,X5) = X2
          | sK5(X0,X1,X2,X3,X4,X5) = X1
          | sK5(X0,X1,X2,X3,X4,X5) = X0
          | r2_hidden(sK5(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
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
              | ~ r2_hidden(X6,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
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
              | ~ r2_hidden(X6,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f542,plain,
    ( ~ r2_hidden(sK2,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))
    | spl6_14 ),
    inference(avatar_component_clause,[],[f541])).

fof(f541,plain,
    ( spl6_14
  <=> r2_hidden(sK2,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f543,plain,
    ( spl6_13
    | ~ spl6_14
    | spl6_12 ),
    inference(avatar_split_clause,[],[f526,f267,f541,f538])).

fof(f267,plain,
    ( spl6_12
  <=> r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f526,plain,
    ( ~ r2_hidden(sK2,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))
    | k1_xboole_0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | spl6_12 ),
    inference(resolution,[],[f520,f268])).

fof(f268,plain,
    ( ~ r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK2)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f267])).

fof(f520,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k4_enumset1(X0,X0,X0,X0,X0,X0) ) ),
    inference(resolution,[],[f519,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f519,plain,(
    ! [X2,X1] :
      ( m1_subset_1(k1_setfam_1(X2),k1_zfmisc_1(X1))
      | k1_xboole_0 = k4_enumset1(X1,X1,X1,X1,X1,X1)
      | ~ r2_hidden(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f517])).

fof(f517,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k4_enumset1(X1,X1,X1,X1,X1,X1)
      | m1_subset_1(k1_setfam_1(X2),k1_zfmisc_1(X1))
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f423,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f87,f107])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f423,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)
      | k1_xboole_0 = k4_enumset1(X0,X0,X0,X0,X0,X0)
      | m1_subset_1(k1_setfam_1(X1),k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f409,f111])).

fof(f409,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_setfam_1(X0),k1_zfmisc_1(k1_setfam_1(X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f401])).

fof(f401,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_setfam_1(X0),k1_zfmisc_1(k1_setfam_1(X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f322,f111])).

fof(f322,plain,(
    ! [X6,X8,X7] :
      ( m1_subset_1(k1_setfam_1(k1_setfam_1(k4_enumset1(X7,X7,X7,X7,X7,X8))),k1_zfmisc_1(k1_setfam_1(X6)))
      | k1_xboole_0 = X6
      | ~ r1_tarski(X6,X8)
      | ~ r1_tarski(X6,X7) ) ),
    inference(resolution,[],[f226,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f226,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k1_setfam_1(k1_setfam_1(k4_enumset1(X5,X5,X5,X5,X5,X4))),k1_setfam_1(X3))
      | ~ r1_tarski(X3,X5)
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f118,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0
      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f84,f108])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f269,plain,
    ( ~ spl6_8
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_12
    | spl6_7 ),
    inference(avatar_split_clause,[],[f264,f237,f267,f161,f153,f242])).

fof(f242,plain,
    ( spl6_8
  <=> v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f153,plain,
    ( spl6_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f161,plain,
    ( spl6_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f237,plain,
    ( spl6_7
  <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f264,plain,
    ( ~ r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))
    | spl6_7 ),
    inference(resolution,[],[f238,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

fof(f238,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f237])).

fof(f263,plain,(
    spl6_9 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | spl6_9 ),
    inference(resolution,[],[f248,f114])).

fof(f114,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f72,f108])).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f248,plain,
    ( ~ r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK1)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl6_9
  <=> r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f254,plain,
    ( ~ spl6_3
    | spl6_8 ),
    inference(avatar_split_clause,[],[f251,f242,f157])).

fof(f157,plain,
    ( spl6_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f251,plain,
    ( ~ v1_relat_1(sK1)
    | spl6_8 ),
    inference(resolution,[],[f250,f185])).

fof(f185,plain,(
    ! [X0,X1] : m1_subset_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f114,f81])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_8 ),
    inference(resolution,[],[f243,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f243,plain,
    ( ~ v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f242])).

fof(f249,plain,
    ( ~ spl6_8
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_9
    | spl6_6 ),
    inference(avatar_split_clause,[],[f240,f234,f247,f161,f157,f242])).

fof(f234,plain,
    ( spl6_6
  <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f240,plain,
    ( ~ r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))
    | spl6_6 ),
    inference(resolution,[],[f235,f65])).

fof(f235,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f234])).

fof(f239,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | spl6_1 ),
    inference(avatar_split_clause,[],[f228,f149,f237,f234])).

fof(f149,plain,
    ( spl6_1
  <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k4_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f228,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2))
    | ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))
    | spl6_1 ),
    inference(resolution,[],[f118,f150])).

fof(f150,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k4_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f149])).

fof(f167,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f64,f165])).

fof(f64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f163,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f60,f161])).

fof(f60,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f42,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

fof(f159,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f61,f157])).

fof(f61,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f155,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f62,f153])).

fof(f62,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f151,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f110,f149])).

fof(f110,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k4_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) ),
    inference(definition_unfolding,[],[f63,f108,f108])).

fof(f63,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (10241)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.50  % (10231)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (10231)Refutation not found, incomplete strategy% (10231)------------------------------
% 0.20/0.51  % (10231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (10239)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (10231)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (10231)Memory used [KB]: 10746
% 0.20/0.51  % (10231)Time elapsed: 0.100 s
% 0.20/0.51  % (10231)------------------------------
% 0.20/0.51  % (10231)------------------------------
% 0.20/0.52  % (10224)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (10249)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (10233)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (10233)Refutation not found, incomplete strategy% (10233)------------------------------
% 0.20/0.52  % (10233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10233)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10233)Memory used [KB]: 10618
% 0.20/0.52  % (10233)Time elapsed: 0.112 s
% 0.20/0.52  % (10233)------------------------------
% 0.20/0.52  % (10233)------------------------------
% 0.20/0.52  % (10229)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (10232)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (10251)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (10247)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (10237)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.39/0.53  % (10228)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.39/0.53  % (10245)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.39/0.53  % (10227)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.39/0.53  % (10245)Refutation not found, incomplete strategy% (10245)------------------------------
% 1.39/0.53  % (10245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.53  % (10245)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.53  
% 1.39/0.53  % (10245)Memory used [KB]: 10746
% 1.39/0.53  % (10245)Time elapsed: 0.097 s
% 1.39/0.53  % (10245)------------------------------
% 1.39/0.53  % (10245)------------------------------
% 1.39/0.54  % (10226)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.39/0.54  % (10225)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.39/0.54  % (10244)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.39/0.54  % (10223)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.39/0.54  % (10230)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.39/0.54  % (10243)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.39/0.54  % (10234)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.39/0.55  % (10235)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.55  % (10236)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.52/0.55  % (10248)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.52/0.55  % (10250)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.52/0.55  % (10252)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.52/0.55  % (10240)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.52/0.56  % (10242)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.52/0.56  % (10240)Refutation not found, incomplete strategy% (10240)------------------------------
% 1.52/0.56  % (10240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (10240)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (10240)Memory used [KB]: 10618
% 1.52/0.56  % (10240)Time elapsed: 0.157 s
% 1.52/0.56  % (10240)------------------------------
% 1.52/0.56  % (10240)------------------------------
% 1.52/0.56  % (10225)Refutation not found, incomplete strategy% (10225)------------------------------
% 1.52/0.56  % (10225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (10225)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (10225)Memory used [KB]: 10746
% 1.52/0.56  % (10225)Time elapsed: 0.134 s
% 1.52/0.56  % (10225)------------------------------
% 1.52/0.56  % (10225)------------------------------
% 1.52/0.56  % (10246)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.52/0.56  % (10244)Refutation not found, incomplete strategy% (10244)------------------------------
% 1.52/0.56  % (10244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (10244)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (10244)Memory used [KB]: 1791
% 1.52/0.56  % (10244)Time elapsed: 0.166 s
% 1.52/0.56  % (10244)------------------------------
% 1.52/0.56  % (10244)------------------------------
% 1.52/0.56  % (10238)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.52/0.61  % (10242)Refutation found. Thanks to Tanya!
% 1.52/0.61  % SZS status Theorem for theBenchmark
% 1.52/0.61  % SZS output start Proof for theBenchmark
% 1.52/0.61  fof(f649,plain,(
% 1.52/0.61    $false),
% 1.52/0.61    inference(avatar_sat_refutation,[],[f151,f155,f159,f163,f167,f239,f249,f254,f263,f269,f543,f546,f621])).
% 1.52/0.61  fof(f621,plain,(
% 1.52/0.61    ~spl6_5 | ~spl6_13),
% 1.52/0.61    inference(avatar_contradiction_clause,[],[f620])).
% 1.52/0.61  fof(f620,plain,(
% 1.52/0.61    $false | (~spl6_5 | ~spl6_13)),
% 1.52/0.61    inference(subsumption_resolution,[],[f289,f619])).
% 1.52/0.61  fof(f619,plain,(
% 1.52/0.61    ( ! [X5] : (~r1_tarski(k1_xboole_0,X5)) ) | (~spl6_5 | ~spl6_13)),
% 1.52/0.61    inference(subsumption_resolution,[],[f566,f618])).
% 1.52/0.61  fof(f618,plain,(
% 1.52/0.61    ( ! [X7] : (~r2_hidden(sK2,X7)) ) | (~spl6_5 | ~spl6_13)),
% 1.52/0.61    inference(trivial_inequality_removal,[],[f617])).
% 1.52/0.61  fof(f617,plain,(
% 1.52/0.61    ( ! [X7] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK2,X7)) ) | (~spl6_5 | ~spl6_13)),
% 1.52/0.61    inference(forward_demodulation,[],[f616,f285])).
% 1.52/0.61  fof(f285,plain,(
% 1.52/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl6_5),
% 1.52/0.61    inference(resolution,[],[f284,f166])).
% 1.52/0.61  fof(f166,plain,(
% 1.52/0.61    v1_xboole_0(k1_xboole_0) | ~spl6_5),
% 1.52/0.61    inference(avatar_component_clause,[],[f165])).
% 1.52/0.61  fof(f165,plain,(
% 1.52/0.61    spl6_5 <=> v1_xboole_0(k1_xboole_0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.52/0.61  fof(f284,plain,(
% 1.52/0.61    ( ! [X0,X1] : (~v1_xboole_0(X0) | k5_xboole_0(X1,X1) = X0) )),
% 1.52/0.61    inference(forward_demodulation,[],[f282,f210])).
% 1.52/0.61  fof(f210,plain,(
% 1.52/0.61    ( ! [X5] : (k5_xboole_0(X5,X5) = k1_setfam_1(k4_enumset1(k5_xboole_0(X5,X5),k5_xboole_0(X5,X5),k5_xboole_0(X5,X5),k5_xboole_0(X5,X5),k5_xboole_0(X5,X5),X5))) )),
% 1.52/0.61    inference(resolution,[],[f117,f196])).
% 1.52/0.61  fof(f196,plain,(
% 1.52/0.61    ( ! [X0] : (r1_tarski(k5_xboole_0(X0,X0),X0)) )),
% 1.52/0.61    inference(superposition,[],[f113,f111])).
% 1.52/0.61  fof(f111,plain,(
% 1.52/0.61    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.52/0.61    inference(definition_unfolding,[],[f69,f108])).
% 1.52/0.61  fof(f108,plain,(
% 1.52/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.52/0.61    inference(definition_unfolding,[],[f73,f107])).
% 1.52/0.61  fof(f107,plain,(
% 1.52/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.52/0.61    inference(definition_unfolding,[],[f74,f106])).
% 1.52/0.61  fof(f106,plain,(
% 1.52/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.52/0.61    inference(definition_unfolding,[],[f83,f105])).
% 1.52/0.61  fof(f105,plain,(
% 1.52/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.52/0.61    inference(definition_unfolding,[],[f91,f92])).
% 1.52/0.61  fof(f92,plain,(
% 1.52/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f15])).
% 1.52/0.61  fof(f15,axiom,(
% 1.52/0.61    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.52/0.61  fof(f91,plain,(
% 1.52/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f14])).
% 1.52/0.61  fof(f14,axiom,(
% 1.52/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.52/0.61  fof(f83,plain,(
% 1.52/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f13])).
% 1.52/0.61  fof(f13,axiom,(
% 1.52/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.52/0.61  fof(f74,plain,(
% 1.52/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f12])).
% 1.52/0.61  fof(f12,axiom,(
% 1.52/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.52/0.61  fof(f73,plain,(
% 1.52/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.52/0.61    inference(cnf_transformation,[],[f19])).
% 1.52/0.61  fof(f19,axiom,(
% 1.52/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.52/0.61  fof(f69,plain,(
% 1.52/0.61    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.52/0.61    inference(cnf_transformation,[],[f26])).
% 1.52/0.61  fof(f26,plain,(
% 1.52/0.61    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.52/0.61    inference(rectify,[],[f3])).
% 1.52/0.61  fof(f3,axiom,(
% 1.52/0.61    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.52/0.61  fof(f113,plain,(
% 1.52/0.61    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X0)) )),
% 1.52/0.61    inference(definition_unfolding,[],[f71,f109])).
% 1.52/0.61  fof(f109,plain,(
% 1.52/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 1.52/0.61    inference(definition_unfolding,[],[f75,f108])).
% 1.52/0.61  fof(f75,plain,(
% 1.52/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.52/0.61    inference(cnf_transformation,[],[f5])).
% 1.52/0.61  fof(f5,axiom,(
% 1.52/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.52/0.61  fof(f71,plain,(
% 1.52/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f9])).
% 1.52/0.61  fof(f9,axiom,(
% 1.52/0.61    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.52/0.61  fof(f117,plain,(
% 1.52/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X0) )),
% 1.52/0.61    inference(definition_unfolding,[],[f78,f108])).
% 1.52/0.61  fof(f78,plain,(
% 1.52/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f33])).
% 1.52/0.61  fof(f33,plain,(
% 1.52/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.52/0.61    inference(ennf_transformation,[],[f8])).
% 1.52/0.61  fof(f8,axiom,(
% 1.52/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.52/0.61  fof(f282,plain,(
% 1.52/0.61    ( ! [X0,X1] : (~v1_xboole_0(X0) | k1_setfam_1(k4_enumset1(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),k5_xboole_0(X1,X1),X1)) = X0) )),
% 1.52/0.61    inference(resolution,[],[f206,f174])).
% 1.52/0.61  fof(f174,plain,(
% 1.52/0.61    ( ! [X2,X1] : (r2_hidden(sK3(X2),X2) | ~v1_xboole_0(X1) | X1 = X2) )),
% 1.52/0.61    inference(resolution,[],[f82,f68])).
% 1.52/0.61  fof(f68,plain,(
% 1.52/0.61    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f47])).
% 1.52/0.61  fof(f47,plain,(
% 1.52/0.61    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.52/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).
% 1.52/0.61  fof(f46,plain,(
% 1.52/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.52/0.61    introduced(choice_axiom,[])).
% 1.52/0.61  fof(f45,plain,(
% 1.52/0.61    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.52/0.61    inference(rectify,[],[f44])).
% 1.52/0.61  fof(f44,plain,(
% 1.52/0.61    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.52/0.61    inference(nnf_transformation,[],[f1])).
% 1.52/0.61  fof(f1,axiom,(
% 1.52/0.61    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.52/0.61  fof(f82,plain,(
% 1.52/0.61    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f36])).
% 1.52/0.61  fof(f36,plain,(
% 1.52/0.61    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.52/0.61    inference(ennf_transformation,[],[f11])).
% 1.52/0.61  fof(f11,axiom,(
% 1.52/0.61    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 1.52/0.61  fof(f206,plain,(
% 1.52/0.61    ( ! [X4,X3] : (~r2_hidden(X3,k1_setfam_1(k4_enumset1(k5_xboole_0(X4,X4),k5_xboole_0(X4,X4),k5_xboole_0(X4,X4),k5_xboole_0(X4,X4),k5_xboole_0(X4,X4),X4)))) )),
% 1.52/0.61    inference(resolution,[],[f115,f193])).
% 1.52/0.61  fof(f193,plain,(
% 1.52/0.61    ( ! [X0] : (r1_xboole_0(k5_xboole_0(X0,X0),X0)) )),
% 1.52/0.61    inference(superposition,[],[f112,f111])).
% 1.52/0.61  fof(f112,plain,(
% 1.52/0.61    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),X1)) )),
% 1.52/0.61    inference(definition_unfolding,[],[f70,f109])).
% 1.52/0.61  fof(f70,plain,(
% 1.52/0.61    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f10])).
% 1.52/0.61  fof(f10,axiom,(
% 1.52/0.61    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.52/0.61  fof(f115,plain,(
% 1.52/0.61    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 1.52/0.61    inference(definition_unfolding,[],[f77,f108])).
% 1.52/0.61  fof(f77,plain,(
% 1.52/0.61    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.52/0.61    inference(cnf_transformation,[],[f49])).
% 1.52/0.61  fof(f49,plain,(
% 1.52/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.52/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f48])).
% 1.52/0.61  fof(f48,plain,(
% 1.52/0.61    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.52/0.61    introduced(choice_axiom,[])).
% 1.52/0.61  fof(f32,plain,(
% 1.52/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.52/0.61    inference(ennf_transformation,[],[f27])).
% 1.52/0.61  fof(f27,plain,(
% 1.52/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.52/0.61    inference(rectify,[],[f4])).
% 1.52/0.61  fof(f4,axiom,(
% 1.52/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.52/0.61  fof(f616,plain,(
% 1.52/0.61    ( ! [X7] : (k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~r2_hidden(sK2,X7)) ) | (~spl6_5 | ~spl6_13)),
% 1.52/0.61    inference(forward_demodulation,[],[f568,f297])).
% 1.52/0.61  fof(f297,plain,(
% 1.52/0.61    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) ) | ~spl6_5),
% 1.52/0.61    inference(resolution,[],[f289,f117])).
% 1.52/0.61  fof(f568,plain,(
% 1.52/0.61    ( ! [X7] : (k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_setfam_1(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X7))) | ~r2_hidden(sK2,X7)) ) | ~spl6_13),
% 1.52/0.61    inference(superposition,[],[f123,f539])).
% 1.52/0.61  fof(f539,plain,(
% 1.52/0.61    k1_xboole_0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) | ~spl6_13),
% 1.52/0.61    inference(avatar_component_clause,[],[f538])).
% 1.52/0.61  fof(f538,plain,(
% 1.52/0.61    spl6_13 <=> k1_xboole_0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.52/0.61  fof(f123,plain,(
% 1.52/0.61    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) != k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k1_setfam_1(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),X2))) | ~r2_hidden(X1,X2)) )),
% 1.52/0.61    inference(definition_unfolding,[],[f89,f107,f109,f107])).
% 1.52/0.61  fof(f89,plain,(
% 1.52/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f54])).
% 1.52/0.61  fof(f54,plain,(
% 1.52/0.61    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.52/0.61    inference(flattening,[],[f53])).
% 1.52/0.61  fof(f53,plain,(
% 1.52/0.61    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.52/0.61    inference(nnf_transformation,[],[f17])).
% 1.52/0.61  fof(f17,axiom,(
% 1.52/0.61    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 1.52/0.61  fof(f566,plain,(
% 1.52/0.61    ( ! [X5] : (~r1_tarski(k1_xboole_0,X5) | r2_hidden(sK2,X5)) ) | ~spl6_13),
% 1.52/0.61    inference(superposition,[],[f120,f539])).
% 1.52/0.61  fof(f120,plain,(
% 1.52/0.61    ( ! [X2,X0,X1] : (~r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 1.52/0.61    inference(definition_unfolding,[],[f86,f107])).
% 1.52/0.61  fof(f86,plain,(
% 1.52/0.61    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f52])).
% 1.52/0.61  fof(f52,plain,(
% 1.52/0.61    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.52/0.61    inference(flattening,[],[f51])).
% 1.52/0.61  fof(f51,plain,(
% 1.52/0.61    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.52/0.61    inference(nnf_transformation,[],[f16])).
% 1.52/0.61  fof(f16,axiom,(
% 1.52/0.61    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.52/0.61  fof(f289,plain,(
% 1.52/0.61    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) ) | ~spl6_5),
% 1.52/0.61    inference(superposition,[],[f196,f285])).
% 1.52/0.61  fof(f546,plain,(
% 1.52/0.61    spl6_14),
% 1.52/0.61    inference(avatar_contradiction_clause,[],[f545])).
% 1.52/0.61  fof(f545,plain,(
% 1.52/0.61    $false | spl6_14),
% 1.52/0.61    inference(resolution,[],[f542,f138])).
% 1.52/0.61  fof(f138,plain,(
% 1.52/0.61    ( ! [X2,X0,X7,X3,X1] : (r2_hidden(X7,k4_enumset1(X0,X0,X1,X2,X3,X7))) )),
% 1.52/0.61    inference(equality_resolution,[],[f137])).
% 1.52/0.61  fof(f137,plain,(
% 1.52/0.61    ( ! [X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | k4_enumset1(X0,X0,X1,X2,X3,X7) != X5) )),
% 1.52/0.61    inference(equality_resolution,[],[f131])).
% 1.52/0.61  fof(f131,plain,(
% 1.52/0.61    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X4 != X7 | k4_enumset1(X0,X0,X1,X2,X3,X4) != X5) )),
% 1.52/0.61    inference(definition_unfolding,[],[f98,f92])).
% 1.52/0.61  fof(f98,plain,(
% 1.52/0.61    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X4 != X7 | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 1.52/0.61    inference(cnf_transformation,[],[f59])).
% 1.52/0.61  fof(f59,plain,(
% 1.52/0.61    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | (((sK5(X0,X1,X2,X3,X4,X5) != X4 & sK5(X0,X1,X2,X3,X4,X5) != X3 & sK5(X0,X1,X2,X3,X4,X5) != X2 & sK5(X0,X1,X2,X3,X4,X5) != X1 & sK5(X0,X1,X2,X3,X4,X5) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5),X5)) & (sK5(X0,X1,X2,X3,X4,X5) = X4 | sK5(X0,X1,X2,X3,X4,X5) = X3 | sK5(X0,X1,X2,X3,X4,X5) = X2 | sK5(X0,X1,X2,X3,X4,X5) = X1 | sK5(X0,X1,X2,X3,X4,X5) = X0 | r2_hidden(sK5(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 1.52/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f57,f58])).
% 1.52/0.61  fof(f58,plain,(
% 1.52/0.61    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5))) => (((sK5(X0,X1,X2,X3,X4,X5) != X4 & sK5(X0,X1,X2,X3,X4,X5) != X3 & sK5(X0,X1,X2,X3,X4,X5) != X2 & sK5(X0,X1,X2,X3,X4,X5) != X1 & sK5(X0,X1,X2,X3,X4,X5) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5),X5)) & (sK5(X0,X1,X2,X3,X4,X5) = X4 | sK5(X0,X1,X2,X3,X4,X5) = X3 | sK5(X0,X1,X2,X3,X4,X5) = X2 | sK5(X0,X1,X2,X3,X4,X5) = X1 | sK5(X0,X1,X2,X3,X4,X5) = X0 | r2_hidden(sK5(X0,X1,X2,X3,X4,X5),X5))))),
% 1.52/0.61    introduced(choice_axiom,[])).
% 1.52/0.61  fof(f57,plain,(
% 1.52/0.61    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 1.52/0.61    inference(rectify,[],[f56])).
% 1.52/0.61  fof(f56,plain,(
% 1.52/0.61    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 1.52/0.61    inference(flattening,[],[f55])).
% 1.52/0.61  fof(f55,plain,(
% 1.52/0.61    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~r2_hidden(X6,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 1.52/0.61    inference(nnf_transformation,[],[f39])).
% 1.52/0.61  fof(f39,plain,(
% 1.52/0.61    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 1.52/0.61    inference(ennf_transformation,[],[f18])).
% 1.52/0.61  fof(f18,axiom,(
% 1.52/0.61    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).
% 1.52/0.61  fof(f542,plain,(
% 1.52/0.61    ~r2_hidden(sK2,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)) | spl6_14),
% 1.52/0.61    inference(avatar_component_clause,[],[f541])).
% 1.52/0.61  fof(f541,plain,(
% 1.52/0.61    spl6_14 <=> r2_hidden(sK2,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.52/0.61  fof(f543,plain,(
% 1.52/0.61    spl6_13 | ~spl6_14 | spl6_12),
% 1.52/0.61    inference(avatar_split_clause,[],[f526,f267,f541,f538])).
% 1.52/0.61  fof(f267,plain,(
% 1.52/0.61    spl6_12 <=> r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK2)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.52/0.61  fof(f526,plain,(
% 1.52/0.61    ~r2_hidden(sK2,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)) | k1_xboole_0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) | spl6_12),
% 1.52/0.61    inference(resolution,[],[f520,f268])).
% 1.52/0.61  fof(f268,plain,(
% 1.52/0.61    ~r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK2) | spl6_12),
% 1.52/0.61    inference(avatar_component_clause,[],[f267])).
% 1.52/0.61  fof(f520,plain,(
% 1.52/0.61    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1) | k1_xboole_0 = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.52/0.61    inference(resolution,[],[f519,f80])).
% 1.52/0.61  fof(f80,plain,(
% 1.52/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f50])).
% 1.52/0.61  fof(f50,plain,(
% 1.52/0.61    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.52/0.61    inference(nnf_transformation,[],[f20])).
% 1.52/0.61  fof(f20,axiom,(
% 1.52/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.52/0.61  fof(f519,plain,(
% 1.52/0.61    ( ! [X2,X1] : (m1_subset_1(k1_setfam_1(X2),k1_zfmisc_1(X1)) | k1_xboole_0 = k4_enumset1(X1,X1,X1,X1,X1,X1) | ~r2_hidden(X1,X2)) )),
% 1.52/0.61    inference(duplicate_literal_removal,[],[f517])).
% 1.52/0.61  fof(f517,plain,(
% 1.52/0.61    ( ! [X2,X1] : (k1_xboole_0 = k4_enumset1(X1,X1,X1,X1,X1,X1) | m1_subset_1(k1_setfam_1(X2),k1_zfmisc_1(X1)) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,X2)) )),
% 1.52/0.61    inference(resolution,[],[f423,f119])).
% 1.52/0.61  fof(f119,plain,(
% 1.52/0.61    ( ! [X2,X0,X1] : (r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.52/0.61    inference(definition_unfolding,[],[f87,f107])).
% 1.52/0.61  fof(f87,plain,(
% 1.52/0.61    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f52])).
% 1.52/0.61  fof(f423,plain,(
% 1.52/0.61    ( ! [X0,X1] : (~r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) | k1_xboole_0 = k4_enumset1(X0,X0,X0,X0,X0,X0) | m1_subset_1(k1_setfam_1(X1),k1_zfmisc_1(X0))) )),
% 1.52/0.61    inference(superposition,[],[f409,f111])).
% 1.52/0.61  fof(f409,plain,(
% 1.52/0.61    ( ! [X0,X1] : (m1_subset_1(k1_setfam_1(X0),k1_zfmisc_1(k1_setfam_1(X1))) | k1_xboole_0 = X1 | ~r1_tarski(X1,X0)) )),
% 1.52/0.61    inference(duplicate_literal_removal,[],[f401])).
% 1.52/0.61  fof(f401,plain,(
% 1.52/0.61    ( ! [X0,X1] : (m1_subset_1(k1_setfam_1(X0),k1_zfmisc_1(k1_setfam_1(X1))) | k1_xboole_0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X1,X0)) )),
% 1.52/0.61    inference(superposition,[],[f322,f111])).
% 1.52/0.61  fof(f322,plain,(
% 1.52/0.61    ( ! [X6,X8,X7] : (m1_subset_1(k1_setfam_1(k1_setfam_1(k4_enumset1(X7,X7,X7,X7,X7,X8))),k1_zfmisc_1(k1_setfam_1(X6))) | k1_xboole_0 = X6 | ~r1_tarski(X6,X8) | ~r1_tarski(X6,X7)) )),
% 1.52/0.61    inference(resolution,[],[f226,f81])).
% 1.52/0.61  fof(f81,plain,(
% 1.52/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.52/0.61    inference(cnf_transformation,[],[f50])).
% 1.52/0.61  fof(f226,plain,(
% 1.52/0.61    ( ! [X4,X5,X3] : (r1_tarski(k1_setfam_1(k1_setfam_1(k4_enumset1(X5,X5,X5,X5,X5,X4))),k1_setfam_1(X3)) | ~r1_tarski(X3,X5) | k1_xboole_0 = X3 | ~r1_tarski(X3,X4)) )),
% 1.52/0.61    inference(resolution,[],[f118,f79])).
% 1.52/0.61  fof(f79,plain,(
% 1.52/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = X0 | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))) )),
% 1.52/0.61    inference(cnf_transformation,[],[f35])).
% 1.52/0.61  fof(f35,plain,(
% 1.52/0.61    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 1.52/0.61    inference(flattening,[],[f34])).
% 1.52/0.61  fof(f34,plain,(
% 1.52/0.61    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 1.52/0.61    inference(ennf_transformation,[],[f21])).
% 1.52/0.61  fof(f21,axiom,(
% 1.52/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).
% 1.52/0.61  fof(f118,plain,(
% 1.52/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.52/0.61    inference(definition_unfolding,[],[f84,f108])).
% 1.52/0.61  fof(f84,plain,(
% 1.52/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f38])).
% 1.52/0.61  fof(f38,plain,(
% 1.52/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.52/0.61    inference(flattening,[],[f37])).
% 1.52/0.61  fof(f37,plain,(
% 1.52/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.52/0.61    inference(ennf_transformation,[],[f7])).
% 1.52/0.61  fof(f7,axiom,(
% 1.52/0.61    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.52/0.61  fof(f269,plain,(
% 1.52/0.61    ~spl6_8 | ~spl6_2 | ~spl6_4 | ~spl6_12 | spl6_7),
% 1.52/0.61    inference(avatar_split_clause,[],[f264,f237,f267,f161,f153,f242])).
% 1.52/0.61  fof(f242,plain,(
% 1.52/0.61    spl6_8 <=> v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.52/0.61  fof(f153,plain,(
% 1.52/0.61    spl6_2 <=> v1_relat_1(sK2)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.52/0.61  fof(f161,plain,(
% 1.52/0.61    spl6_4 <=> v1_relat_1(sK0)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.52/0.61  fof(f237,plain,(
% 1.52/0.61    spl6_7 <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.52/0.61  fof(f264,plain,(
% 1.52/0.61    ~r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK2) | ~v1_relat_1(sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) | spl6_7),
% 1.52/0.61    inference(resolution,[],[f238,f65])).
% 1.52/0.61  fof(f65,plain,(
% 1.52/0.61    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f30])).
% 1.52/0.61  fof(f30,plain,(
% 1.52/0.61    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.52/0.61    inference(flattening,[],[f29])).
% 1.52/0.61  fof(f29,plain,(
% 1.52/0.61    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.52/0.61    inference(ennf_transformation,[],[f23])).
% 1.52/0.61  fof(f23,axiom,(
% 1.52/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).
% 1.52/0.61  fof(f238,plain,(
% 1.52/0.61    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) | spl6_7),
% 1.52/0.61    inference(avatar_component_clause,[],[f237])).
% 1.52/0.61  fof(f263,plain,(
% 1.52/0.61    spl6_9),
% 1.52/0.61    inference(avatar_contradiction_clause,[],[f262])).
% 1.52/0.61  fof(f262,plain,(
% 1.52/0.61    $false | spl6_9),
% 1.52/0.61    inference(resolution,[],[f248,f114])).
% 1.52/0.61  fof(f114,plain,(
% 1.52/0.61    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0)) )),
% 1.52/0.61    inference(definition_unfolding,[],[f72,f108])).
% 1.52/0.61  fof(f72,plain,(
% 1.52/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f6])).
% 1.52/0.61  fof(f6,axiom,(
% 1.52/0.61    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.52/0.61  fof(f248,plain,(
% 1.52/0.61    ~r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK1) | spl6_9),
% 1.52/0.61    inference(avatar_component_clause,[],[f247])).
% 1.52/0.61  fof(f247,plain,(
% 1.52/0.61    spl6_9 <=> r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK1)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.52/0.61  fof(f254,plain,(
% 1.52/0.61    ~spl6_3 | spl6_8),
% 1.52/0.61    inference(avatar_split_clause,[],[f251,f242,f157])).
% 1.52/0.61  fof(f157,plain,(
% 1.52/0.61    spl6_3 <=> v1_relat_1(sK1)),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.52/0.61  fof(f251,plain,(
% 1.52/0.61    ~v1_relat_1(sK1) | spl6_8),
% 1.52/0.61    inference(resolution,[],[f250,f185])).
% 1.52/0.61  fof(f185,plain,(
% 1.52/0.61    ( ! [X0,X1] : (m1_subset_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),k1_zfmisc_1(X0))) )),
% 1.52/0.61    inference(resolution,[],[f114,f81])).
% 1.52/0.61  fof(f250,plain,(
% 1.52/0.61    ( ! [X0] : (~m1_subset_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_8),
% 1.52/0.61    inference(resolution,[],[f243,f66])).
% 1.52/0.61  fof(f66,plain,(
% 1.52/0.61    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.52/0.61    inference(cnf_transformation,[],[f31])).
% 1.52/0.61  fof(f31,plain,(
% 1.52/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.52/0.61    inference(ennf_transformation,[],[f22])).
% 1.52/0.61  fof(f22,axiom,(
% 1.52/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.52/0.61  fof(f243,plain,(
% 1.52/0.61    ~v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) | spl6_8),
% 1.52/0.61    inference(avatar_component_clause,[],[f242])).
% 1.52/0.61  fof(f249,plain,(
% 1.52/0.61    ~spl6_8 | ~spl6_3 | ~spl6_4 | ~spl6_9 | spl6_6),
% 1.52/0.61    inference(avatar_split_clause,[],[f240,f234,f247,f161,f157,f242])).
% 1.52/0.61  fof(f234,plain,(
% 1.52/0.61    spl6_6 <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.52/0.61  fof(f240,plain,(
% 1.52/0.61    ~r1_tarski(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),sK1) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) | spl6_6),
% 1.52/0.61    inference(resolution,[],[f235,f65])).
% 1.52/0.61  fof(f235,plain,(
% 1.52/0.61    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) | spl6_6),
% 1.52/0.61    inference(avatar_component_clause,[],[f234])).
% 1.52/0.61  fof(f239,plain,(
% 1.52/0.61    ~spl6_6 | ~spl6_7 | spl6_1),
% 1.52/0.61    inference(avatar_split_clause,[],[f228,f149,f237,f234])).
% 1.52/0.61  fof(f149,plain,(
% 1.52/0.61    spl6_1 <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k4_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))))),
% 1.52/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.52/0.61  fof(f228,plain,(
% 1.52/0.61    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) | ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) | spl6_1),
% 1.52/0.61    inference(resolution,[],[f118,f150])).
% 1.52/0.61  fof(f150,plain,(
% 1.52/0.61    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k4_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) | spl6_1),
% 1.52/0.61    inference(avatar_component_clause,[],[f149])).
% 1.52/0.61  fof(f167,plain,(
% 1.52/0.61    spl6_5),
% 1.52/0.61    inference(avatar_split_clause,[],[f64,f165])).
% 1.52/0.61  fof(f64,plain,(
% 1.52/0.61    v1_xboole_0(k1_xboole_0)),
% 1.52/0.61    inference(cnf_transformation,[],[f2])).
% 1.52/0.61  fof(f2,axiom,(
% 1.52/0.61    v1_xboole_0(k1_xboole_0)),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.52/0.61  fof(f163,plain,(
% 1.52/0.61    spl6_4),
% 1.52/0.61    inference(avatar_split_clause,[],[f60,f161])).
% 1.52/0.61  fof(f60,plain,(
% 1.52/0.61    v1_relat_1(sK0)),
% 1.52/0.61    inference(cnf_transformation,[],[f43])).
% 1.52/0.61  fof(f43,plain,(
% 1.52/0.61    ((~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.52/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f42,f41,f40])).
% 1.52/0.61  fof(f40,plain,(
% 1.52/0.61    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.52/0.61    introduced(choice_axiom,[])).
% 1.52/0.61  fof(f41,plain,(
% 1.52/0.61    ? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 1.52/0.61    introduced(choice_axiom,[])).
% 1.52/0.61  fof(f42,plain,(
% 1.52/0.61    ? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2))),
% 1.52/0.61    introduced(choice_axiom,[])).
% 1.52/0.61  fof(f28,plain,(
% 1.52/0.61    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.52/0.61    inference(ennf_transformation,[],[f25])).
% 1.52/0.61  fof(f25,negated_conjecture,(
% 1.52/0.61    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 1.52/0.61    inference(negated_conjecture,[],[f24])).
% 1.52/0.61  fof(f24,conjecture,(
% 1.52/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 1.52/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).
% 1.52/0.61  fof(f159,plain,(
% 1.52/0.61    spl6_3),
% 1.52/0.61    inference(avatar_split_clause,[],[f61,f157])).
% 1.52/0.61  fof(f61,plain,(
% 1.52/0.61    v1_relat_1(sK1)),
% 1.52/0.61    inference(cnf_transformation,[],[f43])).
% 1.52/0.61  fof(f155,plain,(
% 1.52/0.61    spl6_2),
% 1.52/0.61    inference(avatar_split_clause,[],[f62,f153])).
% 1.52/0.61  fof(f62,plain,(
% 1.52/0.61    v1_relat_1(sK2)),
% 1.52/0.61    inference(cnf_transformation,[],[f43])).
% 1.52/0.61  fof(f151,plain,(
% 1.52/0.61    ~spl6_1),
% 1.52/0.61    inference(avatar_split_clause,[],[f110,f149])).
% 1.52/0.61  fof(f110,plain,(
% 1.52/0.61    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k4_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))))),
% 1.52/0.61    inference(definition_unfolding,[],[f63,f108,f108])).
% 1.52/0.61  fof(f63,plain,(
% 1.52/0.61    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 1.52/0.61    inference(cnf_transformation,[],[f43])).
% 1.52/0.61  % SZS output end Proof for theBenchmark
% 1.52/0.61  % (10242)------------------------------
% 1.52/0.61  % (10242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.61  % (10242)Termination reason: Refutation
% 1.52/0.61  
% 1.52/0.61  % (10242)Memory used [KB]: 11257
% 1.52/0.61  % (10242)Time elapsed: 0.195 s
% 1.52/0.61  % (10242)------------------------------
% 1.52/0.61  % (10242)------------------------------
% 1.52/0.61  % (10222)Success in time 0.256 s
%------------------------------------------------------------------------------
