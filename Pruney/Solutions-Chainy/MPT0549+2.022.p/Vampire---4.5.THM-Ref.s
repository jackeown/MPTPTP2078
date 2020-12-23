%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:38 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 146 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :   17
%              Number of atoms          :  206 ( 451 expanded)
%              Number of equality atoms :   78 ( 168 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f266,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f67,f123,f263])).

fof(f263,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f261,f34])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k9_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k9_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k9_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k9_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k9_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f261,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f256,f65])).

fof(f65,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl4_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f256,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl4_1 ),
    inference(trivial_inequality_removal,[],[f253])).

fof(f253,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl4_1 ),
    inference(superposition,[],[f48,f244])).

fof(f244,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f179,f241])).

fof(f241,plain,(
    ! [X1] : k1_xboole_0 = k8_relat_1(k1_xboole_0,k7_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f236,f39])).

fof(f39,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f236,plain,(
    ! [X1] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,k7_relat_1(sK1,X1))
      | ~ r1_xboole_0(k7_relat_1(sK1,X1),k1_xboole_0) ) ),
    inference(superposition,[],[f227,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f53,f41])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f227,plain,(
    ! [X0] : k8_relat_1(k1_xboole_0,k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,X0),k1_xboole_0)) ),
    inference(superposition,[],[f223,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f223,plain,(
    ! [X0,X1] : k8_relat_1(X0,k7_relat_1(sK1,X1)) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,X1),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,X1)),X0))) ),
    inference(resolution,[],[f134,f34])).

fof(f134,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X1,k7_relat_1(X2,X3)) = k1_setfam_1(k2_tarski(k7_relat_1(X2,X3),k2_zfmisc_1(k1_relat_1(k7_relat_1(X2,X3)),X1))) ) ),
    inference(resolution,[],[f55,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k1_setfam_1(k2_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f47,f42])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

fof(f179,plain,
    ( k7_relat_1(sK1,sK0) = k8_relat_1(k1_xboole_0,k7_relat_1(sK1,sK0))
    | ~ spl4_1 ),
    inference(superposition,[],[f171,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl4_1
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f171,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k8_relat_1(k9_relat_1(sK1,X0),k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f97,f34])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = k8_relat_1(k9_relat_1(X0,X1),k7_relat_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f96,f45])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,X1) = k8_relat_1(k9_relat_1(X0,X1),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f40,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f40,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f123,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f121,f61])).

fof(f61,plain,
    ( k1_xboole_0 != k9_relat_1(sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f121,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f120,f38])).

fof(f38,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f120,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f117,f34])).

fof(f117,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl4_2 ),
    inference(superposition,[],[f46,f100])).

fof(f100,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f98,f64])).

fof(f64,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f98,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_relat_1(sK1),X0)
      | k1_xboole_0 = k7_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f49,f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f35,f63,f59])).

fof(f35,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f36,f63,f59])).

fof(f36,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:17:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.52  % (8268)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (8276)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.31/0.53  % (8284)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.31/0.53  % (8276)Refutation not found, incomplete strategy% (8276)------------------------------
% 1.31/0.53  % (8276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (8292)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.53  % (8276)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (8276)Memory used [KB]: 10618
% 1.31/0.53  % (8276)Time elapsed: 0.105 s
% 1.31/0.53  % (8276)------------------------------
% 1.31/0.53  % (8276)------------------------------
% 1.31/0.54  % (8268)Refutation not found, incomplete strategy% (8268)------------------------------
% 1.31/0.54  % (8268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (8268)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (8268)Memory used [KB]: 10746
% 1.31/0.54  % (8268)Time elapsed: 0.117 s
% 1.31/0.54  % (8268)------------------------------
% 1.31/0.54  % (8268)------------------------------
% 1.31/0.54  % (8269)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.31/0.54  % (8267)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.54  % (8270)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.54  % (8282)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.54  % (8271)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.54  % (8272)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.31/0.54  % (8269)Refutation found. Thanks to Tanya!
% 1.31/0.54  % SZS status Theorem for theBenchmark
% 1.31/0.54  % SZS output start Proof for theBenchmark
% 1.31/0.54  fof(f266,plain,(
% 1.31/0.54    $false),
% 1.31/0.54    inference(avatar_sat_refutation,[],[f66,f67,f123,f263])).
% 1.31/0.54  fof(f263,plain,(
% 1.31/0.54    ~spl4_1 | spl4_2),
% 1.31/0.54    inference(avatar_contradiction_clause,[],[f262])).
% 1.31/0.54  fof(f262,plain,(
% 1.31/0.54    $false | (~spl4_1 | spl4_2)),
% 1.31/0.54    inference(subsumption_resolution,[],[f261,f34])).
% 1.31/0.54  fof(f34,plain,(
% 1.31/0.54    v1_relat_1(sK1)),
% 1.31/0.54    inference(cnf_transformation,[],[f26])).
% 1.31/0.54  fof(f26,plain,(
% 1.31/0.54    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 1.31/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).
% 1.31/0.54  fof(f25,plain,(
% 1.31/0.54    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 1.31/0.54    introduced(choice_axiom,[])).
% 1.31/0.54  fof(f24,plain,(
% 1.31/0.54    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1))),
% 1.31/0.54    inference(flattening,[],[f23])).
% 1.31/0.54  fof(f23,plain,(
% 1.31/0.54    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0))) & v1_relat_1(X1))),
% 1.31/0.54    inference(nnf_transformation,[],[f15])).
% 1.31/0.54  fof(f15,plain,(
% 1.31/0.54    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.31/0.54    inference(ennf_transformation,[],[f13])).
% 1.31/0.54  fof(f13,negated_conjecture,(
% 1.31/0.54    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.31/0.54    inference(negated_conjecture,[],[f12])).
% 1.31/0.54  fof(f12,conjecture,(
% 1.31/0.54    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 1.31/0.54  fof(f261,plain,(
% 1.31/0.54    ~v1_relat_1(sK1) | (~spl4_1 | spl4_2)),
% 1.31/0.54    inference(subsumption_resolution,[],[f256,f65])).
% 1.31/0.54  fof(f65,plain,(
% 1.31/0.54    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl4_2),
% 1.31/0.54    inference(avatar_component_clause,[],[f63])).
% 1.31/0.54  fof(f63,plain,(
% 1.31/0.54    spl4_2 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.31/0.54  fof(f256,plain,(
% 1.31/0.54    r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | ~spl4_1),
% 1.31/0.54    inference(trivial_inequality_removal,[],[f253])).
% 1.31/0.54  fof(f253,plain,(
% 1.31/0.54    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | ~spl4_1),
% 1.31/0.54    inference(superposition,[],[f48,f244])).
% 1.31/0.54  fof(f244,plain,(
% 1.31/0.54    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl4_1),
% 1.31/0.54    inference(backward_demodulation,[],[f179,f241])).
% 1.31/0.54  fof(f241,plain,(
% 1.31/0.54    ( ! [X1] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,k7_relat_1(sK1,X1))) )),
% 1.31/0.54    inference(subsumption_resolution,[],[f236,f39])).
% 1.31/0.54  fof(f39,plain,(
% 1.31/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f3])).
% 1.31/0.54  fof(f3,axiom,(
% 1.31/0.54    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.31/0.54  fof(f236,plain,(
% 1.31/0.54    ( ! [X1] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,k7_relat_1(sK1,X1)) | ~r1_xboole_0(k7_relat_1(sK1,X1),k1_xboole_0)) )),
% 1.31/0.54    inference(superposition,[],[f227,f78])).
% 1.31/0.54  fof(f78,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.31/0.54    inference(resolution,[],[f53,f41])).
% 1.31/0.54  fof(f41,plain,(
% 1.31/0.54    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.31/0.54    inference(cnf_transformation,[],[f28])).
% 1.31/0.54  fof(f28,plain,(
% 1.31/0.54    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 1.31/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f27])).
% 1.31/0.54  fof(f27,plain,(
% 1.31/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.31/0.54    introduced(choice_axiom,[])).
% 1.31/0.54  fof(f17,plain,(
% 1.31/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.31/0.54    inference(ennf_transformation,[],[f2])).
% 1.31/0.54  fof(f2,axiom,(
% 1.31/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.31/0.54  fof(f53,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.31/0.54    inference(definition_unfolding,[],[f44,f42])).
% 1.31/0.54  fof(f42,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.31/0.54    inference(cnf_transformation,[],[f5])).
% 1.31/0.54  fof(f5,axiom,(
% 1.31/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.31/0.54  fof(f44,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.31/0.54    inference(cnf_transformation,[],[f30])).
% 1.31/0.54  fof(f30,plain,(
% 1.31/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.31/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f29])).
% 1.31/0.54  fof(f29,plain,(
% 1.31/0.54    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.31/0.54    introduced(choice_axiom,[])).
% 1.31/0.54  fof(f18,plain,(
% 1.31/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.31/0.54    inference(ennf_transformation,[],[f14])).
% 1.31/0.54  fof(f14,plain,(
% 1.31/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.31/0.54    inference(rectify,[],[f1])).
% 1.31/0.54  fof(f1,axiom,(
% 1.31/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.31/0.54  fof(f227,plain,(
% 1.31/0.54    ( ! [X0] : (k8_relat_1(k1_xboole_0,k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,X0),k1_xboole_0))) )),
% 1.31/0.54    inference(superposition,[],[f223,f56])).
% 1.31/0.54  fof(f56,plain,(
% 1.31/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.31/0.54    inference(equality_resolution,[],[f52])).
% 1.31/0.54  fof(f52,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.31/0.54    inference(cnf_transformation,[],[f33])).
% 1.31/0.54  fof(f33,plain,(
% 1.31/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.31/0.54    inference(flattening,[],[f32])).
% 1.31/0.54  fof(f32,plain,(
% 1.31/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.31/0.54    inference(nnf_transformation,[],[f4])).
% 1.31/0.54  fof(f4,axiom,(
% 1.31/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.31/0.54  fof(f223,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k8_relat_1(X0,k7_relat_1(sK1,X1)) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,X1),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,X1)),X0)))) )),
% 1.31/0.54    inference(resolution,[],[f134,f34])).
% 1.31/0.54  fof(f134,plain,(
% 1.31/0.54    ( ! [X2,X3,X1] : (~v1_relat_1(X2) | k8_relat_1(X1,k7_relat_1(X2,X3)) = k1_setfam_1(k2_tarski(k7_relat_1(X2,X3),k2_zfmisc_1(k1_relat_1(k7_relat_1(X2,X3)),X1)))) )),
% 1.31/0.54    inference(resolution,[],[f55,f45])).
% 1.31/0.54  fof(f45,plain,(
% 1.31/0.54    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f19])).
% 1.31/0.54  fof(f19,plain,(
% 1.31/0.54    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.31/0.54    inference(ennf_transformation,[],[f6])).
% 1.31/0.54  fof(f6,axiom,(
% 1.31/0.54    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.31/0.54  fof(f55,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k1_setfam_1(k2_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 1.31/0.54    inference(definition_unfolding,[],[f47,f42])).
% 1.31/0.54  fof(f47,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f21])).
% 1.31/0.54  fof(f21,plain,(
% 1.31/0.54    ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.31/0.54    inference(ennf_transformation,[],[f7])).
% 1.31/0.54  fof(f7,axiom,(
% 1.31/0.54    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).
% 1.31/0.54  fof(f179,plain,(
% 1.31/0.54    k7_relat_1(sK1,sK0) = k8_relat_1(k1_xboole_0,k7_relat_1(sK1,sK0)) | ~spl4_1),
% 1.31/0.54    inference(superposition,[],[f171,f60])).
% 1.31/0.54  fof(f60,plain,(
% 1.31/0.54    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl4_1),
% 1.31/0.54    inference(avatar_component_clause,[],[f59])).
% 1.31/0.54  fof(f59,plain,(
% 1.31/0.54    spl4_1 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.31/0.54  fof(f171,plain,(
% 1.31/0.54    ( ! [X0] : (k7_relat_1(sK1,X0) = k8_relat_1(k9_relat_1(sK1,X0),k7_relat_1(sK1,X0))) )),
% 1.31/0.54    inference(resolution,[],[f97,f34])).
% 1.31/0.54  fof(f97,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,X1) = k8_relat_1(k9_relat_1(X0,X1),k7_relat_1(X0,X1))) )),
% 1.31/0.54    inference(subsumption_resolution,[],[f96,f45])).
% 1.31/0.54  fof(f96,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k8_relat_1(k9_relat_1(X0,X1),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.31/0.54    inference(superposition,[],[f40,f46])).
% 1.31/0.54  fof(f46,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f20])).
% 1.31/0.54  fof(f20,plain,(
% 1.31/0.54    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.31/0.54    inference(ennf_transformation,[],[f9])).
% 1.31/0.54  fof(f9,axiom,(
% 1.31/0.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.31/0.54  fof(f40,plain,(
% 1.31/0.54    ( ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f16])).
% 1.31/0.54  fof(f16,plain,(
% 1.31/0.54    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 1.31/0.54    inference(ennf_transformation,[],[f8])).
% 1.31/0.54  fof(f8,axiom,(
% 1.31/0.54    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).
% 1.31/0.54  fof(f48,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k1_xboole_0 != k7_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f31])).
% 1.31/0.54  fof(f31,plain,(
% 1.31/0.54    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.31/0.54    inference(nnf_transformation,[],[f22])).
% 1.31/0.54  fof(f22,plain,(
% 1.31/0.54    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.31/0.54    inference(ennf_transformation,[],[f11])).
% 1.31/0.54  fof(f11,axiom,(
% 1.31/0.54    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 1.31/0.54  fof(f123,plain,(
% 1.31/0.54    spl4_1 | ~spl4_2),
% 1.31/0.54    inference(avatar_contradiction_clause,[],[f122])).
% 1.31/0.54  fof(f122,plain,(
% 1.31/0.54    $false | (spl4_1 | ~spl4_2)),
% 1.31/0.54    inference(subsumption_resolution,[],[f121,f61])).
% 1.31/0.54  fof(f61,plain,(
% 1.31/0.54    k1_xboole_0 != k9_relat_1(sK1,sK0) | spl4_1),
% 1.31/0.54    inference(avatar_component_clause,[],[f59])).
% 1.31/0.54  fof(f121,plain,(
% 1.31/0.54    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl4_2),
% 1.31/0.54    inference(forward_demodulation,[],[f120,f38])).
% 1.31/0.54  fof(f38,plain,(
% 1.31/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.31/0.54    inference(cnf_transformation,[],[f10])).
% 1.31/0.54  fof(f10,axiom,(
% 1.31/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.31/0.54  fof(f120,plain,(
% 1.31/0.54    k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,sK0) | ~spl4_2),
% 1.31/0.54    inference(subsumption_resolution,[],[f117,f34])).
% 1.31/0.54  fof(f117,plain,(
% 1.31/0.54    k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | ~spl4_2),
% 1.31/0.54    inference(superposition,[],[f46,f100])).
% 1.31/0.54  fof(f100,plain,(
% 1.31/0.54    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl4_2),
% 1.31/0.54    inference(resolution,[],[f98,f64])).
% 1.31/0.54  fof(f64,plain,(
% 1.31/0.54    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl4_2),
% 1.31/0.54    inference(avatar_component_clause,[],[f63])).
% 1.31/0.54  fof(f98,plain,(
% 1.31/0.54    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK1),X0) | k1_xboole_0 = k7_relat_1(sK1,X0)) )),
% 1.31/0.54    inference(resolution,[],[f49,f34])).
% 1.31/0.54  fof(f49,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f31])).
% 1.31/0.54  fof(f67,plain,(
% 1.31/0.54    spl4_1 | spl4_2),
% 1.31/0.54    inference(avatar_split_clause,[],[f35,f63,f59])).
% 1.31/0.54  fof(f35,plain,(
% 1.31/0.54    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 1.31/0.54    inference(cnf_transformation,[],[f26])).
% 1.31/0.54  fof(f66,plain,(
% 1.31/0.54    ~spl4_1 | ~spl4_2),
% 1.31/0.54    inference(avatar_split_clause,[],[f36,f63,f59])).
% 1.31/0.54  fof(f36,plain,(
% 1.31/0.54    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)),
% 1.31/0.54    inference(cnf_transformation,[],[f26])).
% 1.31/0.54  % SZS output end Proof for theBenchmark
% 1.31/0.54  % (8269)------------------------------
% 1.31/0.54  % (8269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (8269)Termination reason: Refutation
% 1.31/0.54  
% 1.31/0.54  % (8269)Memory used [KB]: 10874
% 1.31/0.54  % (8269)Time elapsed: 0.133 s
% 1.31/0.54  % (8269)------------------------------
% 1.31/0.54  % (8269)------------------------------
% 1.31/0.54  % (8275)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.31/0.55  % (8281)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.55  % (8294)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.31/0.55  % (8290)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.31/0.55  % (8293)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.31/0.55  % (8295)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.44/0.55  % (8261)Success in time 0.187 s
%------------------------------------------------------------------------------
