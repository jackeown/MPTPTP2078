%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 164 expanded)
%              Number of leaves         :   18 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  199 ( 362 expanded)
%              Number of equality atoms :   65 ( 150 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f64,f97,f99,f130,f133,f161])).

fof(f161,plain,
    ( ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(resolution,[],[f159,f57])).

fof(f57,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl2_1
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f159,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl2_4 ),
    inference(resolution,[],[f115,f95])).

fof(f95,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl2_4
  <=> r1_xboole_0(k2_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f115,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_xboole_0(X4,k3_enumset1(X2,X2,X2,X2,X3))
      | ~ r2_hidden(X3,X4) ) ),
    inference(trivial_inequality_removal,[],[f114])).

fof(f114,plain,(
    ! [X4,X2,X3] :
      ( k3_enumset1(X2,X2,X2,X2,X3) != k3_enumset1(X2,X2,X2,X2,X3)
      | ~ r2_hidden(X3,X4)
      | ~ r1_xboole_0(X4,k3_enumset1(X2,X2,X2,X2,X3)) ) ),
    inference(forward_demodulation,[],[f108,f69])).

fof(f69,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f50,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f30,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f108,plain,(
    ! [X4,X2,X3] :
      ( k3_enumset1(X2,X2,X2,X2,X3) != k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X3),k1_xboole_0)
      | ~ r2_hidden(X3,X4)
      | ~ r1_xboole_0(X4,k3_enumset1(X2,X2,X2,X2,X3)) ) ),
    inference(superposition,[],[f53,f74])).

fof(f74,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = k3_xboole_0(X4,X3)
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(superposition,[],[f38,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X1) != k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2))
      | ~ r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f42,f46,f34,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f133,plain,
    ( ~ spl2_3
    | spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f132,f60,f94,f90])).

fof(f90,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f60,plain,
    ( spl2_2
  <=> k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f132,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f131])).

fof(f131,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f35,f62])).

fof(f62,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f130,plain,
    ( spl2_1
    | spl2_4 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl2_1
    | spl2_4 ),
    inference(resolution,[],[f118,f58])).

fof(f58,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f118,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | spl2_4 ),
    inference(resolution,[],[f106,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f46])).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f106,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1))
    | spl2_4 ),
    inference(resolution,[],[f105,f96])).

fof(f96,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f105,plain,(
    ! [X2,X1] :
      ( r1_xboole_0(X1,X2)
      | ~ r1_xboole_0(X2,X1) ) ),
    inference(trivial_inequality_removal,[],[f102])).

fof(f102,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(X1,X2)
      | ~ r1_xboole_0(X2,X1) ) ),
    inference(superposition,[],[f39,f74])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f99,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f92,f26])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
      | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
    & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
      | r2_hidden(sK0,k2_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
        | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
      & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
        | r2_hidden(sK0,k2_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(f92,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f97,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_2 ),
    inference(avatar_split_clause,[],[f88,f60,f94,f90])).

fof(f88,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK1)
    | spl2_2 ),
    inference(trivial_inequality_removal,[],[f85])).

fof(f85,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK1)
    | spl2_2 ),
    inference(superposition,[],[f61,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f64,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f49,f60,f56])).

fof(f49,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f27,f47])).

fof(f27,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f48,f60,f56])).

fof(f48,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f28,f47])).

fof(f28,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:52 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.42  % (11192)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.43  % (11200)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.43  % (11192)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f162,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f63,f64,f97,f99,f130,f133,f161])).
% 0.21/0.43  fof(f161,plain,(
% 0.21/0.43    ~spl2_1 | ~spl2_4),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f160])).
% 0.21/0.43  fof(f160,plain,(
% 0.21/0.43    $false | (~spl2_1 | ~spl2_4)),
% 0.21/0.43    inference(resolution,[],[f159,f57])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    r2_hidden(sK0,k2_relat_1(sK1)) | ~spl2_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f56])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    spl2_1 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.43  fof(f159,plain,(
% 0.21/0.43    ~r2_hidden(sK0,k2_relat_1(sK1)) | ~spl2_4),
% 0.21/0.43    inference(resolution,[],[f115,f95])).
% 0.21/0.43  fof(f95,plain,(
% 0.21/0.43    r1_xboole_0(k2_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl2_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f94])).
% 0.21/0.43  fof(f94,plain,(
% 0.21/0.43    spl2_4 <=> r1_xboole_0(k2_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.43  fof(f115,plain,(
% 0.21/0.43    ( ! [X4,X2,X3] : (~r1_xboole_0(X4,k3_enumset1(X2,X2,X2,X2,X3)) | ~r2_hidden(X3,X4)) )),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f114])).
% 0.21/0.43  fof(f114,plain,(
% 0.21/0.43    ( ! [X4,X2,X3] : (k3_enumset1(X2,X2,X2,X2,X3) != k3_enumset1(X2,X2,X2,X2,X3) | ~r2_hidden(X3,X4) | ~r1_xboole_0(X4,k3_enumset1(X2,X2,X2,X2,X3))) )),
% 0.21/0.43    inference(forward_demodulation,[],[f108,f69])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.43    inference(forward_demodulation,[],[f50,f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.21/0.43    inference(definition_unfolding,[],[f30,f34])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.43  fof(f108,plain,(
% 0.21/0.43    ( ! [X4,X2,X3] : (k3_enumset1(X2,X2,X2,X2,X3) != k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X3),k1_xboole_0) | ~r2_hidden(X3,X4) | ~r1_xboole_0(X4,k3_enumset1(X2,X2,X2,X2,X3))) )),
% 0.21/0.43    inference(superposition,[],[f53,f74])).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    ( ! [X4,X3] : (k1_xboole_0 = k3_xboole_0(X4,X3) | ~r1_xboole_0(X3,X4)) )),
% 0.21/0.43    inference(superposition,[],[f38,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(nnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) != k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2)) | ~r2_hidden(X1,X2)) )),
% 0.21/0.43    inference(definition_unfolding,[],[f42,f46,f34,f46])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.43    inference(definition_unfolding,[],[f33,f45])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.43    inference(definition_unfolding,[],[f40,f44])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.43    inference(flattening,[],[f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.43    inference(nnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 0.21/0.43  fof(f133,plain,(
% 0.21/0.43    ~spl2_3 | spl2_4 | ~spl2_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f132,f60,f94,f90])).
% 0.21/0.43  fof(f90,plain,(
% 0.21/0.43    spl2_3 <=> v1_relat_1(sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    spl2_2 <=> k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.43  fof(f132,plain,(
% 0.21/0.43    r1_xboole_0(k2_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK1) | ~spl2_2),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f131])).
% 0.21/0.43  fof(f131,plain,(
% 0.21/0.43    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK1) | ~spl2_2),
% 0.21/0.43    inference(superposition,[],[f35,f62])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl2_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f60])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(nnf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 0.21/0.43  fof(f130,plain,(
% 0.21/0.43    spl2_1 | spl2_4),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f129])).
% 0.21/0.43  fof(f129,plain,(
% 0.21/0.43    $false | (spl2_1 | spl2_4)),
% 0.21/0.43    inference(resolution,[],[f118,f58])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    ~r2_hidden(sK0,k2_relat_1(sK1)) | spl2_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f56])).
% 0.21/0.43  fof(f118,plain,(
% 0.21/0.43    r2_hidden(sK0,k2_relat_1(sK1)) | spl2_4),
% 0.21/0.43    inference(resolution,[],[f106,f51])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.43    inference(definition_unfolding,[],[f37,f47])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.21/0.43    inference(definition_unfolding,[],[f31,f46])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,axiom,(
% 0.21/0.43    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.43  fof(f106,plain,(
% 0.21/0.43    ~r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1)) | spl2_4),
% 0.21/0.43    inference(resolution,[],[f105,f96])).
% 0.21/0.43  fof(f96,plain,(
% 0.21/0.43    ~r1_xboole_0(k2_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl2_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f94])).
% 0.21/0.43  fof(f105,plain,(
% 0.21/0.43    ( ! [X2,X1] : (r1_xboole_0(X1,X2) | ~r1_xboole_0(X2,X1)) )),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f102])).
% 0.21/0.43  fof(f102,plain,(
% 0.21/0.43    ( ! [X2,X1] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(X1,X2) | ~r1_xboole_0(X2,X1)) )),
% 0.21/0.43    inference(superposition,[],[f39,f74])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f23])).
% 0.21/0.43  fof(f99,plain,(
% 0.21/0.43    spl2_3),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f98])).
% 0.21/0.43  fof(f98,plain,(
% 0.21/0.43    $false | spl2_3),
% 0.21/0.43    inference(resolution,[],[f92,f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    v1_relat_1(sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    (k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.43    inference(flattening,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ? [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1)))) & v1_relat_1(X1))),
% 0.21/0.43    inference(nnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) & v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.21/0.43    inference(negated_conjecture,[],[f13])).
% 0.21/0.43  fof(f13,conjecture,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).
% 0.21/0.43  fof(f92,plain,(
% 0.21/0.43    ~v1_relat_1(sK1) | spl2_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f90])).
% 0.21/0.43  fof(f97,plain,(
% 0.21/0.43    ~spl2_3 | ~spl2_4 | spl2_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f88,f60,f94,f90])).
% 0.21/0.43  fof(f88,plain,(
% 0.21/0.43    ~r1_xboole_0(k2_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK1) | spl2_2),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f85])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k2_relat_1(sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK1) | spl2_2),
% 0.21/0.43    inference(superposition,[],[f61,f36])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f22])).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    k1_xboole_0 != k10_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl2_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f60])).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    spl2_1 | ~spl2_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f49,f60,f56])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    k1_xboole_0 != k10_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.43    inference(definition_unfolding,[],[f27,f47])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    ~spl2_1 | spl2_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f48,f60,f56])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    k1_xboole_0 = k10_relat_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.43    inference(definition_unfolding,[],[f28,f47])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (11192)------------------------------
% 0.21/0.43  % (11192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (11192)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (11192)Memory used [KB]: 6140
% 0.21/0.43  % (11192)Time elapsed: 0.036 s
% 0.21/0.43  % (11192)------------------------------
% 0.21/0.43  % (11192)------------------------------
% 0.21/0.43  % (11187)Success in time 0.073 s
%------------------------------------------------------------------------------
