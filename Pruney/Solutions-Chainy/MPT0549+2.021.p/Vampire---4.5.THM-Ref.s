%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:38 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 152 expanded)
%              Number of leaves         :   20 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :  259 ( 477 expanded)
%              Number of equality atoms :   78 ( 158 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f364,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f75,f296,f312,f358,f363])).

fof(f363,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f362])).

fof(f362,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f361,f72])).

fof(f72,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f361,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f360,f37])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k9_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k9_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).

% (5147)Refutation not found, incomplete strategy% (5147)------------------------------
% (5147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5147)Termination reason: Refutation not found, incomplete strategy

% (5147)Memory used [KB]: 10618
% (5147)Time elapsed: 0.153 s
% (5147)------------------------------
% (5147)------------------------------
fof(f28,plain,
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

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f360,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f359])).

fof(f359,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK1)
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl4_1 ),
    inference(superposition,[],[f69,f140])).

fof(f140,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k9_relat_1(X2,X3)
      | ~ v1_relat_1(X2)
      | ~ r1_xboole_0(k1_relat_1(X2),X3) ) ),
    inference(forward_demodulation,[],[f138,f41])).

fof(f41,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f138,plain,(
    ! [X2,X3] :
      ( k2_relat_1(k1_xboole_0) = k9_relat_1(X2,X3)
      | ~ v1_relat_1(X2)
      | ~ r1_xboole_0(k1_relat_1(X2),X3) ) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,(
    ! [X2,X3] :
      ( k2_relat_1(k1_xboole_0) = k9_relat_1(X2,X3)
      | ~ v1_relat_1(X2)
      | ~ r1_xboole_0(k1_relat_1(X2),X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f53,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f69,plain,
    ( k1_xboole_0 != k9_relat_1(sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_1
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f358,plain,
    ( spl4_2
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f357,f292,f71])).

fof(f292,plain,
    ( spl4_11
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f357,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f349,f37])).

fof(f349,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl4_11 ),
    inference(trivial_inequality_removal,[],[f346])).

fof(f346,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl4_11 ),
    inference(superposition,[],[f55,f294])).

fof(f294,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f292])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f312,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | spl4_10 ),
    inference(subsumption_resolution,[],[f309,f37])).

fof(f309,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_10 ),
    inference(resolution,[],[f290,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f290,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl4_10
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f296,plain,
    ( ~ spl4_10
    | spl4_11
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f283,f67,f292,f288])).

fof(f283,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl4_1 ),
    inference(superposition,[],[f222,f280])).

fof(f280,plain,
    ( k7_relat_1(sK1,sK0) = k8_relat_1(k1_xboole_0,k7_relat_1(sK1,sK0))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f275,f37])).

fof(f275,plain,
    ( k7_relat_1(sK1,sK0) = k8_relat_1(k1_xboole_0,k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl4_1 ),
    inference(superposition,[],[f133,f68])).

fof(f68,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f133,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,X1) = k8_relat_1(k9_relat_1(X0,X1),k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f132,f52])).

fof(f132,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,X1) = k8_relat_1(k9_relat_1(X0,X1),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f45,f53])).

fof(f45,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

fof(f222,plain,(
    ! [X1] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f214,f42])).

fof(f42,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f214,plain,(
    ! [X1] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X1)
      | ~ v1_relat_1(X1)
      | ~ r1_xboole_0(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f178,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f89,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f60,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f178,plain,(
    ! [X0] :
      ( k8_relat_1(k1_xboole_0,X0) = k1_setfam_1(k2_tarski(X0,k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f62,f64])).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k1_setfam_1(k2_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f54,f46])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

fof(f75,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f38,f71,f67])).

fof(f38,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f39,f71,f67])).

fof(f39,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:54:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (5130)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (5133)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (5135)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (5134)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (5145)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (5132)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (5131)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (5143)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (5152)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (5150)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (5148)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (5137)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (5141)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (5144)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (5141)Refutation not found, incomplete strategy% (5141)------------------------------
% 0.22/0.53  % (5141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (5152)Refutation not found, incomplete strategy% (5152)------------------------------
% 0.22/0.53  % (5152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (5140)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (5142)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (5138)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (5139)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (5154)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (5152)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (5152)Memory used [KB]: 10618
% 0.22/0.53  % (5155)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (5152)Time elapsed: 0.092 s
% 0.22/0.53  % (5152)------------------------------
% 0.22/0.53  % (5152)------------------------------
% 0.22/0.53  % (5157)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (5136)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (5159)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (5153)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (5140)Refutation not found, incomplete strategy% (5140)------------------------------
% 0.22/0.54  % (5140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (5140)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (5140)Memory used [KB]: 10618
% 0.22/0.54  % (5140)Time elapsed: 0.144 s
% 0.22/0.54  % (5140)------------------------------
% 0.22/0.54  % (5140)------------------------------
% 0.22/0.54  % (5149)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (5151)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (5158)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (5156)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.55  % (5141)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (5141)Memory used [KB]: 10618
% 1.41/0.55  % (5141)Time elapsed: 0.135 s
% 1.41/0.55  % (5141)------------------------------
% 1.41/0.55  % (5141)------------------------------
% 1.41/0.55  % (5146)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.55  % (5157)Refutation found. Thanks to Tanya!
% 1.41/0.55  % SZS status Theorem for theBenchmark
% 1.41/0.55  % (5147)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.55  % SZS output start Proof for theBenchmark
% 1.41/0.55  fof(f364,plain,(
% 1.41/0.55    $false),
% 1.41/0.55    inference(avatar_sat_refutation,[],[f74,f75,f296,f312,f358,f363])).
% 1.41/0.55  fof(f363,plain,(
% 1.41/0.55    spl4_1 | ~spl4_2),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f362])).
% 1.41/0.55  fof(f362,plain,(
% 1.41/0.55    $false | (spl4_1 | ~spl4_2)),
% 1.41/0.55    inference(subsumption_resolution,[],[f361,f72])).
% 1.41/0.55  fof(f72,plain,(
% 1.41/0.55    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl4_2),
% 1.41/0.55    inference(avatar_component_clause,[],[f71])).
% 1.41/0.55  fof(f71,plain,(
% 1.41/0.55    spl4_2 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.41/0.55  fof(f361,plain,(
% 1.41/0.55    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl4_1),
% 1.41/0.55    inference(subsumption_resolution,[],[f360,f37])).
% 1.41/0.55  fof(f37,plain,(
% 1.41/0.55    v1_relat_1(sK1)),
% 1.41/0.55    inference(cnf_transformation,[],[f29])).
% 1.41/0.55  fof(f29,plain,(
% 1.41/0.55    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).
% 1.41/0.55  % (5147)Refutation not found, incomplete strategy% (5147)------------------------------
% 1.41/0.55  % (5147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (5147)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (5147)Memory used [KB]: 10618
% 1.41/0.55  % (5147)Time elapsed: 0.153 s
% 1.41/0.55  % (5147)------------------------------
% 1.41/0.55  % (5147)------------------------------
% 1.41/0.55  fof(f28,plain,(
% 1.41/0.55    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f27,plain,(
% 1.41/0.55    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1))),
% 1.41/0.55    inference(flattening,[],[f26])).
% 1.41/0.55  fof(f26,plain,(
% 1.41/0.55    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0))) & v1_relat_1(X1))),
% 1.41/0.55    inference(nnf_transformation,[],[f17])).
% 1.41/0.55  fof(f17,plain,(
% 1.41/0.55    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.41/0.55    inference(ennf_transformation,[],[f14])).
% 1.41/0.55  fof(f14,negated_conjecture,(
% 1.41/0.55    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.41/0.55    inference(negated_conjecture,[],[f13])).
% 1.41/0.55  fof(f13,conjecture,(
% 1.41/0.55    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 1.41/0.55  fof(f360,plain,(
% 1.41/0.55    ~v1_relat_1(sK1) | ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl4_1),
% 1.41/0.55    inference(trivial_inequality_removal,[],[f359])).
% 1.41/0.55  fof(f359,plain,(
% 1.41/0.55    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK1) | ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl4_1),
% 1.41/0.55    inference(superposition,[],[f69,f140])).
% 1.41/0.55  fof(f140,plain,(
% 1.41/0.55    ( ! [X2,X3] : (k1_xboole_0 = k9_relat_1(X2,X3) | ~v1_relat_1(X2) | ~r1_xboole_0(k1_relat_1(X2),X3)) )),
% 1.41/0.55    inference(forward_demodulation,[],[f138,f41])).
% 1.41/0.55  fof(f41,plain,(
% 1.41/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.41/0.55    inference(cnf_transformation,[],[f11])).
% 1.41/0.55  fof(f11,axiom,(
% 1.41/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.41/0.55  fof(f138,plain,(
% 1.41/0.55    ( ! [X2,X3] : (k2_relat_1(k1_xboole_0) = k9_relat_1(X2,X3) | ~v1_relat_1(X2) | ~r1_xboole_0(k1_relat_1(X2),X3)) )),
% 1.41/0.55    inference(duplicate_literal_removal,[],[f135])).
% 1.41/0.55  fof(f135,plain,(
% 1.41/0.55    ( ! [X2,X3] : (k2_relat_1(k1_xboole_0) = k9_relat_1(X2,X3) | ~v1_relat_1(X2) | ~r1_xboole_0(k1_relat_1(X2),X3) | ~v1_relat_1(X2)) )),
% 1.41/0.55    inference(superposition,[],[f53,f56])).
% 1.41/0.55  fof(f56,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f34])).
% 1.41/0.55  fof(f34,plain,(
% 1.41/0.55    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.41/0.55    inference(nnf_transformation,[],[f25])).
% 1.41/0.55  fof(f25,plain,(
% 1.41/0.55    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.41/0.55    inference(ennf_transformation,[],[f12])).
% 1.41/0.55  fof(f12,axiom,(
% 1.41/0.55    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 1.41/0.55  fof(f53,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f23])).
% 1.41/0.55  fof(f23,plain,(
% 1.41/0.55    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.41/0.55    inference(ennf_transformation,[],[f10])).
% 1.41/0.55  fof(f10,axiom,(
% 1.41/0.55    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.41/0.55  fof(f69,plain,(
% 1.41/0.55    k1_xboole_0 != k9_relat_1(sK1,sK0) | spl4_1),
% 1.41/0.55    inference(avatar_component_clause,[],[f67])).
% 1.41/0.55  fof(f67,plain,(
% 1.41/0.55    spl4_1 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.41/0.55  fof(f358,plain,(
% 1.41/0.55    spl4_2 | ~spl4_11),
% 1.41/0.55    inference(avatar_split_clause,[],[f357,f292,f71])).
% 1.41/0.55  fof(f292,plain,(
% 1.41/0.55    spl4_11 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.41/0.55  fof(f357,plain,(
% 1.41/0.55    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl4_11),
% 1.41/0.55    inference(subsumption_resolution,[],[f349,f37])).
% 1.41/0.55  fof(f349,plain,(
% 1.41/0.55    r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | ~spl4_11),
% 1.41/0.55    inference(trivial_inequality_removal,[],[f346])).
% 1.41/0.55  fof(f346,plain,(
% 1.41/0.55    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | ~spl4_11),
% 1.41/0.55    inference(superposition,[],[f55,f294])).
% 1.41/0.55  fof(f294,plain,(
% 1.41/0.55    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl4_11),
% 1.41/0.55    inference(avatar_component_clause,[],[f292])).
% 1.41/0.55  fof(f55,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k1_xboole_0 != k7_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f34])).
% 1.41/0.55  fof(f312,plain,(
% 1.41/0.55    spl4_10),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f311])).
% 1.41/0.55  fof(f311,plain,(
% 1.41/0.55    $false | spl4_10),
% 1.41/0.55    inference(subsumption_resolution,[],[f309,f37])).
% 1.41/0.55  fof(f309,plain,(
% 1.41/0.55    ~v1_relat_1(sK1) | spl4_10),
% 1.41/0.55    inference(resolution,[],[f290,f52])).
% 1.41/0.55  fof(f52,plain,(
% 1.41/0.55    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f22])).
% 1.41/0.55  fof(f22,plain,(
% 1.41/0.55    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(ennf_transformation,[],[f7])).
% 1.41/0.55  fof(f7,axiom,(
% 1.41/0.55    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.41/0.55  fof(f290,plain,(
% 1.41/0.55    ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl4_10),
% 1.41/0.55    inference(avatar_component_clause,[],[f288])).
% 1.41/0.55  fof(f288,plain,(
% 1.41/0.55    spl4_10 <=> v1_relat_1(k7_relat_1(sK1,sK0))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.41/0.55  fof(f296,plain,(
% 1.41/0.55    ~spl4_10 | spl4_11 | ~spl4_1),
% 1.41/0.55    inference(avatar_split_clause,[],[f283,f67,f292,f288])).
% 1.41/0.55  fof(f283,plain,(
% 1.41/0.55    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl4_1),
% 1.41/0.55    inference(superposition,[],[f222,f280])).
% 1.41/0.55  fof(f280,plain,(
% 1.41/0.55    k7_relat_1(sK1,sK0) = k8_relat_1(k1_xboole_0,k7_relat_1(sK1,sK0)) | ~spl4_1),
% 1.41/0.55    inference(subsumption_resolution,[],[f275,f37])).
% 1.41/0.55  fof(f275,plain,(
% 1.41/0.55    k7_relat_1(sK1,sK0) = k8_relat_1(k1_xboole_0,k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | ~spl4_1),
% 1.41/0.55    inference(superposition,[],[f133,f68])).
% 1.41/0.55  fof(f68,plain,(
% 1.41/0.55    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl4_1),
% 1.41/0.55    inference(avatar_component_clause,[],[f67])).
% 1.41/0.55  fof(f133,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k8_relat_1(k9_relat_1(X0,X1),k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f132,f52])).
% 1.41/0.55  fof(f132,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k8_relat_1(k9_relat_1(X0,X1),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(superposition,[],[f45,f53])).
% 1.41/0.55  fof(f45,plain,(
% 1.41/0.55    ( ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f19])).
% 1.41/0.55  fof(f19,plain,(
% 1.41/0.55    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 1.41/0.55    inference(ennf_transformation,[],[f9])).
% 1.41/0.55  fof(f9,axiom,(
% 1.41/0.55    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).
% 1.41/0.55  fof(f222,plain,(
% 1.41/0.55    ( ! [X1] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,X1) | ~v1_relat_1(X1)) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f214,f42])).
% 1.41/0.55  fof(f42,plain,(
% 1.41/0.55    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f3])).
% 1.41/0.55  fof(f3,axiom,(
% 1.41/0.55    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.41/0.55  fof(f214,plain,(
% 1.41/0.55    ( ! [X1] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,X1) | ~v1_relat_1(X1) | ~r1_xboole_0(X1,k1_xboole_0)) )),
% 1.41/0.55    inference(superposition,[],[f178,f91])).
% 1.41/0.55  fof(f91,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.41/0.55    inference(resolution,[],[f89,f44])).
% 1.41/0.55  fof(f44,plain,(
% 1.41/0.55    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.41/0.55    inference(cnf_transformation,[],[f18])).
% 1.41/0.55  fof(f18,plain,(
% 1.41/0.55    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f4])).
% 1.41/0.55  fof(f4,axiom,(
% 1.41/0.55    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.41/0.55  fof(f89,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (r1_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X2) | ~r1_xboole_0(X0,X1)) )),
% 1.41/0.55    inference(resolution,[],[f60,f49])).
% 1.41/0.55  fof(f49,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f33])).
% 1.41/0.55  fof(f33,plain,(
% 1.41/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f32])).
% 1.41/0.55  fof(f32,plain,(
% 1.41/0.55    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f21,plain,(
% 1.41/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.41/0.55    inference(ennf_transformation,[],[f16])).
% 1.41/0.55  fof(f16,plain,(
% 1.41/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.41/0.55    inference(rectify,[],[f1])).
% 1.41/0.55  fof(f1,axiom,(
% 1.41/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.41/0.55  fof(f60,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.41/0.55    inference(definition_unfolding,[],[f48,f46])).
% 1.41/0.56  fof(f46,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f6])).
% 1.41/0.56  fof(f6,axiom,(
% 1.41/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.41/0.56  fof(f48,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f31])).
% 1.41/0.56  fof(f31,plain,(
% 1.41/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.41/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f30])).
% 1.41/0.56  fof(f30,plain,(
% 1.41/0.56    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f20,plain,(
% 1.41/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.41/0.56    inference(ennf_transformation,[],[f15])).
% 1.41/0.56  fof(f15,plain,(
% 1.41/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.41/0.56    inference(rectify,[],[f2])).
% 1.41/0.56  fof(f2,axiom,(
% 1.41/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.41/0.56  fof(f178,plain,(
% 1.41/0.56    ( ! [X0] : (k8_relat_1(k1_xboole_0,X0) = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 1.41/0.56    inference(superposition,[],[f62,f64])).
% 1.41/0.56  fof(f64,plain,(
% 1.41/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.41/0.56    inference(equality_resolution,[],[f59])).
% 1.41/0.56  fof(f59,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.41/0.56    inference(cnf_transformation,[],[f36])).
% 1.41/0.56  fof(f36,plain,(
% 1.41/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.41/0.56    inference(flattening,[],[f35])).
% 1.41/0.56  fof(f35,plain,(
% 1.41/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.41/0.56    inference(nnf_transformation,[],[f5])).
% 1.41/0.56  fof(f5,axiom,(
% 1.41/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.41/0.56  fof(f62,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k1_setfam_1(k2_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 1.41/0.56    inference(definition_unfolding,[],[f54,f46])).
% 1.41/0.56  fof(f54,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f24])).
% 1.41/0.56  fof(f24,plain,(
% 1.41/0.56    ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.41/0.56    inference(ennf_transformation,[],[f8])).
% 1.41/0.56  fof(f8,axiom,(
% 1.41/0.56    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).
% 1.41/0.56  fof(f75,plain,(
% 1.41/0.56    spl4_1 | spl4_2),
% 1.41/0.56    inference(avatar_split_clause,[],[f38,f71,f67])).
% 1.41/0.56  fof(f38,plain,(
% 1.41/0.56    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 1.41/0.56    inference(cnf_transformation,[],[f29])).
% 1.41/0.56  fof(f74,plain,(
% 1.41/0.56    ~spl4_1 | ~spl4_2),
% 1.41/0.56    inference(avatar_split_clause,[],[f39,f71,f67])).
% 1.41/0.56  fof(f39,plain,(
% 1.41/0.56    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)),
% 1.41/0.56    inference(cnf_transformation,[],[f29])).
% 1.41/0.56  % SZS output end Proof for theBenchmark
% 1.41/0.56  % (5157)------------------------------
% 1.41/0.56  % (5157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (5157)Termination reason: Refutation
% 1.41/0.56  
% 1.41/0.56  % (5157)Memory used [KB]: 6396
% 1.41/0.56  % (5157)Time elapsed: 0.158 s
% 1.41/0.56  % (5157)------------------------------
% 1.41/0.56  % (5157)------------------------------
% 1.41/0.56  % (5129)Success in time 0.194 s
%------------------------------------------------------------------------------
