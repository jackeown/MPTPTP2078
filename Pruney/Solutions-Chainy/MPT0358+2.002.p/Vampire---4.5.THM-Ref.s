%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 229 expanded)
%              Number of leaves         :   24 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :  258 ( 561 expanded)
%              Number of equality atoms :   48 ( 176 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f275,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f73,f78,f187,f189,f221,f231,f274])).

fof(f274,plain,
    ( spl4_2
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | spl4_2
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f272])).

fof(f272,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_2
    | ~ spl4_5 ),
    inference(superposition,[],[f71,f240])).

fof(f240,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_5 ),
    inference(superposition,[],[f228,f93])).

fof(f93,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f88,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f88,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f53,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f228,plain,
    ( ! [X2] : sK1 = k3_xboole_0(sK1,X2)
    | ~ spl4_5 ),
    inference(resolution,[],[f224,f53])).

fof(f224,plain,
    ( ! [X0] : r1_tarski(sK1,X0)
    | ~ spl4_5 ),
    inference(resolution,[],[f127,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f127,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl4_5
  <=> ! [X2] : ~ r2_hidden(X2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f71,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f231,plain,
    ( ~ spl4_8
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl4_8
    | spl4_10 ),
    inference(resolution,[],[f220,f211])).

fof(f211,plain,
    ( r1_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f205,f204])).

fof(f204,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f143,f197])).

fof(f197,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl4_8 ),
    inference(superposition,[],[f191,f49])).

fof(f191,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl4_8 ),
    inference(resolution,[],[f186,f53])).

fof(f186,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl4_8
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f143,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f63,f38])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( sK1 != k1_subset_1(sK0)
      | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & ( sK1 = k1_subset_1(sK0)
      | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k1_subset_1(sK0)
        | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & ( sK1 = k1_subset_1(sK0)
        | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f205,plain,
    ( r1_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f203,f197])).

fof(f203,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1))
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f150,f197])).

fof(f150,plain,(
    r1_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f148,f49])).

fof(f148,plain,(
    r1_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK1),sK0),k3_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f79,f143])).

fof(f79,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f50,f49])).

fof(f50,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f220,plain,
    ( ~ r1_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl4_10
  <=> r1_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f221,plain,
    ( spl4_5
    | ~ spl4_10
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f213,f184,f65,f218,f126])).

fof(f65,plain,
    ( spl4_1
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK1,k5_xboole_0(sK0,sK1))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(resolution,[],[f206,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(resolution,[],[f52,f46])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f206,plain,
    ( r1_tarski(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f66,f204])).

fof(f66,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f189,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | spl4_7 ),
    inference(resolution,[],[f182,f41])).

fof(f182,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl4_7
  <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f187,plain,
    ( ~ spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f178,f184,f180])).

fof(f178,plain,
    ( r1_tarski(sK1,sK0)
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f177,f62])).

fof(f62,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f43,f59])).

fof(f59,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f45,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f45,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f43,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f177,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f174,f44])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f174,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r1_tarski(sK1,k3_subset_1(sK0,X0))
      | ~ r1_tarski(X0,k3_subset_1(sK0,sK1)) ) ),
    inference(resolution,[],[f55,f38])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(f78,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(resolution,[],[f41,f76])).

fof(f76,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f75,f62])).

fof(f75,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))
    | spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f67,f70])).

fof(f70,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f67,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f73,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f61,f69,f65])).

fof(f61,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f39,f42])).

fof(f39,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f60,f69,f65])).

fof(f60,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f40,f42])).

fof(f40,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n009.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 18:28:11 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.22/0.50  % (17961)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.50  % (17960)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (17960)Refutation not found, incomplete strategy% (17960)------------------------------
% 0.22/0.50  % (17960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (17960)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (17960)Memory used [KB]: 6268
% 0.22/0.50  % (17960)Time elapsed: 0.100 s
% 0.22/0.50  % (17960)------------------------------
% 0.22/0.50  % (17960)------------------------------
% 0.22/0.51  % (17986)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.51  % (17969)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % (17966)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.51  % (17971)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (17977)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.51  % (17963)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (17984)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.52  % (17965)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (17968)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (17980)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (17959)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (17958)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (17977)Refutation not found, incomplete strategy% (17977)------------------------------
% 0.22/0.52  % (17977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17977)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (17977)Memory used [KB]: 10746
% 0.22/0.52  % (17977)Time elapsed: 0.113 s
% 0.22/0.52  % (17977)------------------------------
% 0.22/0.52  % (17977)------------------------------
% 0.22/0.52  % (17962)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (17968)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f275,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f72,f73,f78,f187,f189,f221,f231,f274])).
% 0.22/0.53  fof(f274,plain,(
% 0.22/0.53    spl4_2 | ~spl4_5),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f273])).
% 0.22/0.53  fof(f273,plain,(
% 0.22/0.53    $false | (spl4_2 | ~spl4_5)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f272])).
% 0.22/0.53  fof(f272,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | (spl4_2 | ~spl4_5)),
% 0.22/0.53    inference(superposition,[],[f71,f240])).
% 0.22/0.53  fof(f240,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | ~spl4_5),
% 0.22/0.53    inference(superposition,[],[f228,f93])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 0.22/0.53    inference(superposition,[],[f88,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(resolution,[],[f53,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.53  fof(f228,plain,(
% 0.22/0.53    ( ! [X2] : (sK1 = k3_xboole_0(sK1,X2)) ) | ~spl4_5),
% 0.22/0.53    inference(resolution,[],[f224,f53])).
% 0.22/0.53  fof(f224,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(sK1,X0)) ) | ~spl4_5),
% 0.22/0.53    inference(resolution,[],[f127,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    ( ! [X2] : (~r2_hidden(X2,sK1)) ) | ~spl4_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f126])).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    spl4_5 <=> ! [X2] : ~r2_hidden(X2,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    k1_xboole_0 != sK1 | spl4_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    spl4_2 <=> k1_xboole_0 = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.53  fof(f231,plain,(
% 0.22/0.53    ~spl4_8 | spl4_10),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f230])).
% 0.22/0.53  fof(f230,plain,(
% 0.22/0.53    $false | (~spl4_8 | spl4_10)),
% 0.22/0.53    inference(resolution,[],[f220,f211])).
% 0.22/0.53  fof(f211,plain,(
% 0.22/0.53    r1_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | ~spl4_8),
% 0.22/0.53    inference(backward_demodulation,[],[f205,f204])).
% 0.22/0.53  fof(f204,plain,(
% 0.22/0.53    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) | ~spl4_8),
% 0.22/0.53    inference(backward_demodulation,[],[f143,f197])).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    sK1 = k3_xboole_0(sK0,sK1) | ~spl4_8),
% 0.22/0.53    inference(superposition,[],[f191,f49])).
% 0.22/0.53  fof(f191,plain,(
% 0.22/0.53    sK1 = k3_xboole_0(sK1,sK0) | ~spl4_8),
% 0.22/0.53    inference(resolution,[],[f186,f53])).
% 0.22/0.53  fof(f186,plain,(
% 0.22/0.53    r1_tarski(sK1,sK0) | ~spl4_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f184])).
% 0.22/0.53  fof(f184,plain,(
% 0.22/0.53    spl4_8 <=> r1_tarski(sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.53    inference(resolution,[],[f63,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    (sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(flattening,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(nnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.22/0.53    inference(negated_conjecture,[],[f16])).
% 0.22/0.53  fof(f16,conjecture,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f54,f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.53  fof(f205,plain,(
% 0.22/0.53    r1_xboole_0(sK1,k3_subset_1(sK0,sK1)) | ~spl4_8),
% 0.22/0.53    inference(forward_demodulation,[],[f203,f197])).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    r1_xboole_0(k3_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1)) | ~spl4_8),
% 0.22/0.53    inference(backward_demodulation,[],[f150,f197])).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    r1_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_subset_1(sK0,sK1))),
% 0.22/0.53    inference(forward_demodulation,[],[f148,f49])).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    r1_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK1),sK0),k3_subset_1(sK0,sK1))),
% 0.22/0.53    inference(superposition,[],[f79,f143])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(superposition,[],[f50,f49])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 0.22/0.53  fof(f220,plain,(
% 0.22/0.53    ~r1_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | spl4_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f218])).
% 0.22/0.53  fof(f218,plain,(
% 0.22/0.53    spl4_10 <=> r1_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.53  fof(f221,plain,(
% 0.22/0.53    spl4_5 | ~spl4_10 | ~spl4_1 | ~spl4_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f213,f184,f65,f218,f126])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    spl4_1 <=> r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.53  fof(f213,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | ~r2_hidden(X0,sK1)) ) | (~spl4_1 | ~spl4_8)),
% 0.22/0.53    inference(resolution,[],[f206,f87])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.53    inference(resolution,[],[f52,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.53    inference(rectify,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.53    inference(nnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.22/0.53    inference(flattening,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.22/0.53  fof(f206,plain,(
% 0.22/0.53    r1_tarski(sK1,k5_xboole_0(sK0,sK1)) | (~spl4_1 | ~spl4_8)),
% 0.22/0.53    inference(backward_demodulation,[],[f66,f204])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | ~spl4_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f65])).
% 0.22/0.53  fof(f189,plain,(
% 0.22/0.53    spl4_7),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f188])).
% 0.22/0.53  fof(f188,plain,(
% 0.22/0.53    $false | spl4_7),
% 0.22/0.53    inference(resolution,[],[f182,f41])).
% 0.22/0.53  fof(f182,plain,(
% 0.22/0.53    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1)) | spl4_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f180])).
% 0.22/0.53  fof(f180,plain,(
% 0.22/0.53    spl4_7 <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.53  fof(f187,plain,(
% 0.22/0.53    ~spl4_7 | spl4_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f178,f184,f180])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    r1_tarski(sK1,sK0) | ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1))),
% 0.22/0.53    inference(forward_demodulation,[],[f177,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.53    inference(definition_unfolding,[],[f43,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f45,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    r1_tarski(sK1,k3_subset_1(sK0,k1_xboole_0)) | ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1))),
% 0.22/0.53    inference(resolution,[],[f174,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,axiom,(
% 0.22/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(sK1,k3_subset_1(sK0,X0)) | ~r1_tarski(X0,k3_subset_1(sK0,sK1))) )),
% 0.22/0.53    inference(resolution,[],[f55,f38])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_tarski(X2,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(flattening,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    spl4_1 | ~spl4_2),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    $false | (spl4_1 | ~spl4_2)),
% 0.22/0.53    inference(resolution,[],[f41,f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ~r1_tarski(k1_xboole_0,sK0) | (spl4_1 | ~spl4_2)),
% 0.22/0.53    inference(forward_demodulation,[],[f75,f62])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) | (spl4_1 | ~spl4_2)),
% 0.22/0.53    inference(forward_demodulation,[],[f67,f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | ~spl4_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f69])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ~r1_tarski(sK1,k3_subset_1(sK0,sK1)) | spl4_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f65])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    spl4_1 | spl4_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f61,f69,f65])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.53    inference(definition_unfolding,[],[f39,f42])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ~spl4_1 | ~spl4_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f60,f69,f65])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.53    inference(definition_unfolding,[],[f40,f42])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (17968)------------------------------
% 0.22/0.53  % (17968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (17968)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (17968)Memory used [KB]: 6268
% 0.22/0.53  % (17968)Time elapsed: 0.121 s
% 0.22/0.53  % (17968)------------------------------
% 0.22/0.53  % (17968)------------------------------
% 0.22/0.53  % (17967)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (17979)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (17953)Success in time 0.171 s
%------------------------------------------------------------------------------
