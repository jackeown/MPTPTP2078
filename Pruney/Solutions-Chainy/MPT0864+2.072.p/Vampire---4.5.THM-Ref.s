%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:41 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  101 (1655 expanded)
%              Number of leaves         :   20 ( 543 expanded)
%              Depth                    :   17
%              Number of atoms          :  198 (2119 expanded)
%              Number of equality atoms :  110 (1776 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f119,f135])).

fof(f135,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f133,f108])).

fof(f108,plain,(
    ! [X1] : r2_hidden(X1,k2_enumset1(X1,X1,X1,X1)) ),
    inference(subsumption_resolution,[],[f106,f102])).

fof(f102,plain,(
    ! [X1] : k1_xboole_0 != k2_enumset1(X1,X1,X1,X1) ),
    inference(forward_demodulation,[],[f101,f90])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f89,f60])).

fof(f60,plain,(
    ! [X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f40,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f50])).

fof(f50,plain,(
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
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X0))) ),
    inference(superposition,[],[f61,f59])).

fof(f59,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f39,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f54])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f61,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))))) ),
    inference(definition_unfolding,[],[f41,f57,f55])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f45,f56])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f101,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(forward_demodulation,[],[f69,f60])).

fof(f69,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_setfam_1(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_setfam_1(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f48,f58,f57,f58,f58])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f54])).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f106,plain,(
    ! [X1] :
      ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ) ),
    inference(superposition,[],[f37,f104])).

% (2826)Refutation not found, incomplete strategy% (2826)------------------------------
% (2826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f104,plain,(
    ! [X0] : sK4(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(subsumption_resolution,[],[f103,f102])).

fof(f103,plain,(
    ! [X0] :
      ( sK4(k2_enumset1(X0,X0,X0,X0)) = X0
      | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) ) ),
    inference(resolution,[],[f100,f37])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_enumset1(X0,X0,X0,X0))
      | X0 = X1 ) ),
    inference(subsumption_resolution,[],[f99,f91])).

fof(f91,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f88,f90])).

fof(f88,plain,(
    ! [X0] : ~ r2_hidden(X0,k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) ),
    inference(superposition,[],[f70,f60])).

fof(f70,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X2,X2,X2,X2))))) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X2,X2,X2,X2))))) ) ),
    inference(definition_unfolding,[],[f52,f57,f58])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f99,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_xboole_0)
      | X0 = X1
      | ~ r2_hidden(X1,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(forward_demodulation,[],[f98,f90])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)))
      | X0 = X1
      | ~ r2_hidden(X1,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(superposition,[],[f64,f60])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X2,X2,X2,X2)))))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f57,f58])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( sP0(sK4(X0),X0)
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP0(sK4(X0),X0)
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ! [X2,X3] :
          ( k4_tarski(X2,X3) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f133,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f127,f107])).

fof(f107,plain,(
    ! [X0] : sP0(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(subsumption_resolution,[],[f105,f102])).

fof(f105,plain,(
    ! [X0] :
      ( sP0(X0,k2_enumset1(X0,X0,X0,X0))
      | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) ) ),
    inference(superposition,[],[f38,f104])).

fof(f38,plain,(
    ! [X0] :
      ( sP0(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ sP0(sK1,X0)
        | ~ r2_hidden(sK1,X0) )
    | ~ spl5_1 ),
    inference(superposition,[],[f68,f125])).

fof(f125,plain,
    ( sK1 = k4_tarski(sK1,sK3)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f32,f124])).

fof(f124,plain,
    ( sK1 = sK2
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f80,f74])).

fof(f74,plain,
    ( sK1 = k1_mcart_1(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl5_1
  <=> sK1 = k1_mcart_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f80,plain,(
    k1_mcart_1(sK1) = sK2 ),
    inference(superposition,[],[f46,f32])).

fof(f46,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

% (2826)Termination reason: Refutation not found, incomplete strategy
fof(f12,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

% (2826)Memory used [KB]: 10618
% (2826)Time elapsed: 0.098 s
fof(f32,plain,(
    sK1 = k4_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

% (2826)------------------------------
% (2826)------------------------------
% (2821)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f24,plain,
    ( ( sK1 = k2_mcart_1(sK1)
      | sK1 = k1_mcart_1(sK1) )
    & sK1 = k4_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK1 = k2_mcart_1(sK1)
        | sK1 = k1_mcart_1(sK1) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK1 ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK1
   => sK1 = k4_tarski(sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f68,plain,(
    ! [X2,X3,X1] :
      ( ~ sP0(k4_tarski(X2,X3),X1)
      | ~ r2_hidden(X2,X1) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X2,X3) != X0
      | ~ r2_hidden(X2,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( k4_tarski(X2,X3) != X0
          | ( ~ r2_hidden(X3,X1)
            & ~ r2_hidden(X2,X1) ) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ! [X2,X3] :
          ( k4_tarski(X2,X3) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP0(X1,X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f119,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f112,f108])).

fof(f112,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_2 ),
    inference(resolution,[],[f107,f86])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ sP0(sK1,X0)
        | ~ r2_hidden(sK1,X0) )
    | ~ spl5_2 ),
    inference(superposition,[],[f67,f83])).

fof(f83,plain,
    ( sK1 = k4_tarski(sK2,sK1)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f32,f82])).

fof(f82,plain,
    ( sK1 = sK3
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f81,f78])).

fof(f78,plain,
    ( sK1 = k2_mcart_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl5_2
  <=> sK1 = k2_mcart_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f81,plain,(
    k2_mcart_1(sK1) = sK3 ),
    inference(superposition,[],[f47,f32])).

fof(f47,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X2,X3,X1] :
      ( ~ sP0(k4_tarski(X2,X3),X1)
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X2,X3) != X0
      | ~ r2_hidden(X3,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f79,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f33,f76,f72])).

fof(f33,plain,
    ( sK1 = k2_mcart_1(sK1)
    | sK1 = k1_mcart_1(sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 15:05:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.48  % (2816)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.18/0.48  % (2816)Refutation not found, incomplete strategy% (2816)------------------------------
% 0.18/0.48  % (2816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (2826)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.18/0.48  % (2816)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.48  
% 0.18/0.48  % (2816)Memory used [KB]: 1663
% 0.18/0.48  % (2816)Time elapsed: 0.084 s
% 0.18/0.48  % (2816)------------------------------
% 0.18/0.48  % (2816)------------------------------
% 0.18/0.49  % (2843)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.18/0.49  % (2843)Refutation found. Thanks to Tanya!
% 0.18/0.49  % SZS status Theorem for theBenchmark
% 0.18/0.49  % (2831)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.18/0.49  % SZS output start Proof for theBenchmark
% 0.18/0.49  fof(f136,plain,(
% 0.18/0.49    $false),
% 0.18/0.49    inference(avatar_sat_refutation,[],[f79,f119,f135])).
% 0.18/0.49  fof(f135,plain,(
% 0.18/0.49    ~spl5_1),
% 0.18/0.49    inference(avatar_contradiction_clause,[],[f134])).
% 0.18/0.49  fof(f134,plain,(
% 0.18/0.49    $false | ~spl5_1),
% 0.18/0.49    inference(subsumption_resolution,[],[f133,f108])).
% 0.18/0.49  fof(f108,plain,(
% 0.18/0.49    ( ! [X1] : (r2_hidden(X1,k2_enumset1(X1,X1,X1,X1))) )),
% 0.18/0.49    inference(subsumption_resolution,[],[f106,f102])).
% 0.18/0.49  fof(f102,plain,(
% 0.18/0.49    ( ! [X1] : (k1_xboole_0 != k2_enumset1(X1,X1,X1,X1)) )),
% 0.18/0.49    inference(forward_demodulation,[],[f101,f90])).
% 0.18/0.49  fof(f90,plain,(
% 0.18/0.49    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.18/0.49    inference(forward_demodulation,[],[f89,f60])).
% 0.18/0.49  fof(f60,plain,(
% 0.18/0.49    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.18/0.49    inference(definition_unfolding,[],[f40,f56])).
% 0.18/0.49  fof(f56,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.18/0.49    inference(definition_unfolding,[],[f43,f54])).
% 0.18/0.49  fof(f54,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.18/0.49    inference(definition_unfolding,[],[f44,f50])).
% 0.18/0.49  fof(f50,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f7])).
% 0.18/0.49  fof(f7,axiom,(
% 0.18/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.18/0.49  fof(f44,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f6])).
% 0.18/0.49  fof(f6,axiom,(
% 0.18/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.18/0.49  fof(f43,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.18/0.49    inference(cnf_transformation,[],[f11])).
% 0.18/0.49  fof(f11,axiom,(
% 0.18/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.18/0.49  fof(f40,plain,(
% 0.18/0.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.18/0.49    inference(cnf_transformation,[],[f17])).
% 0.18/0.49  fof(f17,plain,(
% 0.18/0.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.18/0.49    inference(rectify,[],[f2])).
% 0.18/0.49  fof(f2,axiom,(
% 0.18/0.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.18/0.49  fof(f89,plain,(
% 0.18/0.49    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X0)))) )),
% 0.18/0.49    inference(superposition,[],[f61,f59])).
% 0.18/0.49  fof(f59,plain,(
% 0.18/0.49    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.18/0.49    inference(definition_unfolding,[],[f39,f55])).
% 0.18/0.49  fof(f55,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.18/0.49    inference(definition_unfolding,[],[f42,f54])).
% 0.18/0.49  fof(f42,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.18/0.49    inference(cnf_transformation,[],[f8])).
% 0.18/0.49  fof(f8,axiom,(
% 0.18/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.18/0.49  fof(f39,plain,(
% 0.18/0.49    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.18/0.49    inference(cnf_transformation,[],[f16])).
% 0.18/0.49  fof(f16,plain,(
% 0.18/0.49    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.18/0.49    inference(rectify,[],[f1])).
% 0.18/0.49  fof(f1,axiom,(
% 0.18/0.49    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.18/0.49  fof(f61,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))))) )),
% 0.18/0.49    inference(definition_unfolding,[],[f41,f57,f55])).
% 0.18/0.49  fof(f57,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.18/0.49    inference(definition_unfolding,[],[f45,f56])).
% 0.18/0.49  fof(f45,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.18/0.49    inference(cnf_transformation,[],[f3])).
% 0.18/0.49  fof(f3,axiom,(
% 0.18/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.18/0.49  fof(f41,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.18/0.49    inference(cnf_transformation,[],[f4])).
% 0.18/0.49  fof(f4,axiom,(
% 0.18/0.49    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.18/0.49  fof(f101,plain,(
% 0.18/0.49    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 0.18/0.49    inference(forward_demodulation,[],[f69,f60])).
% 0.18/0.49  fof(f69,plain,(
% 0.18/0.49    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_setfam_1(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))))) )),
% 0.18/0.49    inference(equality_resolution,[],[f63])).
% 0.18/0.49  fof(f63,plain,(
% 0.18/0.49    ( ! [X0,X1] : (X0 != X1 | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_setfam_1(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))))) )),
% 0.18/0.49    inference(definition_unfolding,[],[f48,f58,f57,f58,f58])).
% 0.18/0.49  fof(f58,plain,(
% 0.18/0.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.18/0.49    inference(definition_unfolding,[],[f34,f54])).
% 0.18/0.49  fof(f34,plain,(
% 0.18/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f5])).
% 0.18/0.49  fof(f5,axiom,(
% 0.18/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.18/0.49  fof(f48,plain,(
% 0.18/0.49    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.18/0.49    inference(cnf_transformation,[],[f29])).
% 0.18/0.49  fof(f29,plain,(
% 0.18/0.49    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.18/0.49    inference(nnf_transformation,[],[f9])).
% 0.18/0.49  fof(f9,axiom,(
% 0.18/0.49    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.18/0.49  fof(f106,plain,(
% 0.18/0.49    ( ! [X1] : (r2_hidden(X1,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1)) )),
% 0.18/0.49    inference(superposition,[],[f37,f104])).
% 0.18/0.49  % (2826)Refutation not found, incomplete strategy% (2826)------------------------------
% 0.18/0.49  % (2826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  fof(f104,plain,(
% 0.18/0.49    ( ! [X0] : (sK4(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.18/0.49    inference(subsumption_resolution,[],[f103,f102])).
% 0.18/0.49  fof(f103,plain,(
% 0.18/0.49    ( ! [X0] : (sK4(k2_enumset1(X0,X0,X0,X0)) = X0 | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0)) )),
% 0.18/0.49    inference(resolution,[],[f100,f37])).
% 0.18/0.49  fof(f100,plain,(
% 0.18/0.49    ( ! [X0,X1] : (~r2_hidden(X1,k2_enumset1(X0,X0,X0,X0)) | X0 = X1) )),
% 0.18/0.49    inference(subsumption_resolution,[],[f99,f91])).
% 0.18/0.49  fof(f91,plain,(
% 0.18/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.18/0.49    inference(backward_demodulation,[],[f88,f90])).
% 0.18/0.49  fof(f88,plain,(
% 0.18/0.49    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)))) )),
% 0.18/0.49    inference(superposition,[],[f70,f60])).
% 0.18/0.49  fof(f70,plain,(
% 0.18/0.49    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X2,X2,X2,X2)))))) )),
% 0.18/0.49    inference(equality_resolution,[],[f65])).
% 0.18/0.49  fof(f65,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X2,X2,X2,X2)))))) )),
% 0.18/0.49    inference(definition_unfolding,[],[f52,f57,f58])).
% 0.18/0.49  fof(f52,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.18/0.49    inference(cnf_transformation,[],[f31])).
% 0.18/0.49  fof(f31,plain,(
% 0.18/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.18/0.49    inference(flattening,[],[f30])).
% 0.18/0.49  fof(f30,plain,(
% 0.18/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.18/0.49    inference(nnf_transformation,[],[f10])).
% 0.18/0.49  fof(f10,axiom,(
% 0.18/0.49    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.18/0.49  fof(f99,plain,(
% 0.18/0.49    ( ! [X0,X1] : (r2_hidden(X1,k1_xboole_0) | X0 = X1 | ~r2_hidden(X1,k2_enumset1(X0,X0,X0,X0))) )),
% 0.18/0.49    inference(forward_demodulation,[],[f98,f90])).
% 0.18/0.49  fof(f98,plain,(
% 0.18/0.49    ( ! [X0,X1] : (r2_hidden(X1,k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0))) | X0 = X1 | ~r2_hidden(X1,k2_enumset1(X0,X0,X0,X0))) )),
% 0.18/0.49    inference(superposition,[],[f64,f60])).
% 0.18/0.49  fof(f64,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X2,X2,X2,X2))))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 0.18/0.49    inference(definition_unfolding,[],[f53,f57,f58])).
% 0.18/0.49  fof(f53,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f31])).
% 0.18/0.49  fof(f37,plain,(
% 0.18/0.49    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.18/0.49    inference(cnf_transformation,[],[f28])).
% 0.18/0.49  fof(f28,plain,(
% 0.18/0.49    ! [X0] : ((sP0(sK4(X0),X0) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 0.18/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f27])).
% 0.18/0.49  fof(f27,plain,(
% 0.18/0.49    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) => (sP0(sK4(X0),X0) & r2_hidden(sK4(X0),X0)))),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f21,plain,(
% 0.18/0.49    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.18/0.49    inference(definition_folding,[],[f19,f20])).
% 0.18/0.49  fof(f20,plain,(
% 0.18/0.49    ! [X1,X0] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP0(X1,X0))),
% 0.18/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.18/0.49  fof(f19,plain,(
% 0.18/0.49    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.18/0.49    inference(ennf_transformation,[],[f13])).
% 0.18/0.49  fof(f13,axiom,(
% 0.18/0.49    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.18/0.49  fof(f133,plain,(
% 0.18/0.49    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_1),
% 0.18/0.49    inference(resolution,[],[f127,f107])).
% 0.18/0.49  fof(f107,plain,(
% 0.18/0.49    ( ! [X0] : (sP0(X0,k2_enumset1(X0,X0,X0,X0))) )),
% 0.18/0.49    inference(subsumption_resolution,[],[f105,f102])).
% 0.18/0.49  fof(f105,plain,(
% 0.18/0.49    ( ! [X0] : (sP0(X0,k2_enumset1(X0,X0,X0,X0)) | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0)) )),
% 0.18/0.49    inference(superposition,[],[f38,f104])).
% 0.18/0.49  fof(f38,plain,(
% 0.18/0.49    ( ! [X0] : (sP0(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.18/0.49    inference(cnf_transformation,[],[f28])).
% 0.18/0.49  fof(f127,plain,(
% 0.18/0.49    ( ! [X0] : (~sP0(sK1,X0) | ~r2_hidden(sK1,X0)) ) | ~spl5_1),
% 0.18/0.49    inference(superposition,[],[f68,f125])).
% 0.18/0.49  fof(f125,plain,(
% 0.18/0.49    sK1 = k4_tarski(sK1,sK3) | ~spl5_1),
% 0.18/0.49    inference(backward_demodulation,[],[f32,f124])).
% 0.18/0.49  fof(f124,plain,(
% 0.18/0.49    sK1 = sK2 | ~spl5_1),
% 0.18/0.49    inference(backward_demodulation,[],[f80,f74])).
% 0.18/0.49  fof(f74,plain,(
% 0.18/0.49    sK1 = k1_mcart_1(sK1) | ~spl5_1),
% 0.18/0.49    inference(avatar_component_clause,[],[f72])).
% 0.18/0.49  fof(f72,plain,(
% 0.18/0.49    spl5_1 <=> sK1 = k1_mcart_1(sK1)),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.18/0.49  fof(f80,plain,(
% 0.18/0.49    k1_mcart_1(sK1) = sK2),
% 0.18/0.49    inference(superposition,[],[f46,f32])).
% 0.18/0.49  fof(f46,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.18/0.49    inference(cnf_transformation,[],[f12])).
% 0.18/0.49  % (2826)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.49  fof(f12,axiom,(
% 0.18/0.49    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.18/0.49  
% 0.18/0.49  % (2826)Memory used [KB]: 10618
% 0.18/0.49  % (2826)Time elapsed: 0.098 s
% 0.18/0.49  fof(f32,plain,(
% 0.18/0.49    sK1 = k4_tarski(sK2,sK3)),
% 0.18/0.49    inference(cnf_transformation,[],[f24])).
% 0.18/0.49  % (2826)------------------------------
% 0.18/0.49  % (2826)------------------------------
% 0.18/0.49  % (2821)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.18/0.49  fof(f24,plain,(
% 0.18/0.49    (sK1 = k2_mcart_1(sK1) | sK1 = k1_mcart_1(sK1)) & sK1 = k4_tarski(sK2,sK3)),
% 0.18/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f23,f22])).
% 0.18/0.49  fof(f22,plain,(
% 0.18/0.49    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK1 = k2_mcart_1(sK1) | sK1 = k1_mcart_1(sK1)) & ? [X2,X1] : k4_tarski(X1,X2) = sK1)),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f23,plain,(
% 0.18/0.49    ? [X2,X1] : k4_tarski(X1,X2) = sK1 => sK1 = k4_tarski(sK2,sK3)),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f18,plain,(
% 0.18/0.49    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.18/0.49    inference(ennf_transformation,[],[f15])).
% 0.18/0.49  fof(f15,negated_conjecture,(
% 0.18/0.49    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.18/0.49    inference(negated_conjecture,[],[f14])).
% 0.18/0.49  fof(f14,conjecture,(
% 0.18/0.49    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.18/0.49  fof(f68,plain,(
% 0.18/0.49    ( ! [X2,X3,X1] : (~sP0(k4_tarski(X2,X3),X1) | ~r2_hidden(X2,X1)) )),
% 0.18/0.49    inference(equality_resolution,[],[f35])).
% 0.18/0.49  fof(f35,plain,(
% 0.18/0.49    ( ! [X2,X0,X3,X1] : (k4_tarski(X2,X3) != X0 | ~r2_hidden(X2,X1) | ~sP0(X0,X1)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f26])).
% 0.18/0.49  fof(f26,plain,(
% 0.18/0.49    ! [X0,X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X0 | (~r2_hidden(X3,X1) & ~r2_hidden(X2,X1))) | ~sP0(X0,X1))),
% 0.18/0.49    inference(rectify,[],[f25])).
% 0.18/0.49  fof(f25,plain,(
% 0.18/0.49    ! [X1,X0] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP0(X1,X0))),
% 0.18/0.49    inference(nnf_transformation,[],[f20])).
% 0.18/0.49  fof(f119,plain,(
% 0.18/0.49    ~spl5_2),
% 0.18/0.49    inference(avatar_contradiction_clause,[],[f117])).
% 0.18/0.49  fof(f117,plain,(
% 0.18/0.49    $false | ~spl5_2),
% 0.18/0.49    inference(subsumption_resolution,[],[f112,f108])).
% 0.18/0.49  fof(f112,plain,(
% 0.18/0.49    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_2),
% 0.18/0.49    inference(resolution,[],[f107,f86])).
% 0.18/0.49  fof(f86,plain,(
% 0.18/0.49    ( ! [X0] : (~sP0(sK1,X0) | ~r2_hidden(sK1,X0)) ) | ~spl5_2),
% 0.18/0.49    inference(superposition,[],[f67,f83])).
% 0.18/0.49  fof(f83,plain,(
% 0.18/0.49    sK1 = k4_tarski(sK2,sK1) | ~spl5_2),
% 0.18/0.49    inference(backward_demodulation,[],[f32,f82])).
% 0.18/0.49  fof(f82,plain,(
% 0.18/0.49    sK1 = sK3 | ~spl5_2),
% 0.18/0.49    inference(forward_demodulation,[],[f81,f78])).
% 0.18/0.49  fof(f78,plain,(
% 0.18/0.49    sK1 = k2_mcart_1(sK1) | ~spl5_2),
% 0.18/0.49    inference(avatar_component_clause,[],[f76])).
% 0.18/0.49  fof(f76,plain,(
% 0.18/0.49    spl5_2 <=> sK1 = k2_mcart_1(sK1)),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.18/0.49  fof(f81,plain,(
% 0.18/0.49    k2_mcart_1(sK1) = sK3),
% 0.18/0.49    inference(superposition,[],[f47,f32])).
% 0.18/0.49  fof(f47,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.18/0.49    inference(cnf_transformation,[],[f12])).
% 0.18/0.49  fof(f67,plain,(
% 0.18/0.49    ( ! [X2,X3,X1] : (~sP0(k4_tarski(X2,X3),X1) | ~r2_hidden(X3,X1)) )),
% 0.18/0.49    inference(equality_resolution,[],[f36])).
% 0.18/0.49  fof(f36,plain,(
% 0.18/0.49    ( ! [X2,X0,X3,X1] : (k4_tarski(X2,X3) != X0 | ~r2_hidden(X3,X1) | ~sP0(X0,X1)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f26])).
% 0.18/0.49  fof(f79,plain,(
% 0.18/0.49    spl5_1 | spl5_2),
% 0.18/0.49    inference(avatar_split_clause,[],[f33,f76,f72])).
% 0.18/0.49  fof(f33,plain,(
% 0.18/0.49    sK1 = k2_mcart_1(sK1) | sK1 = k1_mcart_1(sK1)),
% 0.18/0.49    inference(cnf_transformation,[],[f24])).
% 0.18/0.49  % SZS output end Proof for theBenchmark
% 0.18/0.49  % (2843)------------------------------
% 0.18/0.49  % (2843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (2843)Termination reason: Refutation
% 0.18/0.49  
% 0.18/0.49  % (2843)Memory used [KB]: 6268
% 0.18/0.49  % (2843)Time elapsed: 0.105 s
% 0.18/0.49  % (2843)------------------------------
% 0.18/0.49  % (2843)------------------------------
% 0.18/0.50  % (2815)Success in time 0.152 s
%------------------------------------------------------------------------------
