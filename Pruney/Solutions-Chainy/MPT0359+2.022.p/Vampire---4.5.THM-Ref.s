%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:41 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 483 expanded)
%              Number of leaves         :   19 ( 142 expanded)
%              Depth                    :   26
%              Number of atoms          :  248 (1326 expanded)
%              Number of equality atoms :   83 ( 478 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f617,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f69,f105,f583])).

fof(f583,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f582])).

% (12216)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f582,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f581,f66])).

fof(f66,plain,
    ( sK0 != sK1
    | spl3_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f581,plain,
    ( sK0 = sK1
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f548,f37])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f548,plain,
    ( sK1 = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f343,f512])).

fof(f512,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f505,f220])).

fof(f220,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f217,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f217,plain,(
    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f53,f125])).

fof(f125,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f116,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f116,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f110,f57])).

fof(f57,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f110,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f33,f30,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

% (12216)Refutation not found, incomplete strategy% (12216)------------------------------
% (12216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12216)Termination reason: Refutation not found, incomplete strategy

% (12216)Memory used [KB]: 10618
% (12216)Time elapsed: 0.146 s
% (12216)------------------------------
% (12216)------------------------------
fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k2_subset_1(sK0)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( sK1 = k2_subset_1(sK0)
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(f33,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

% (12236)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f505,plain,
    ( k4_xboole_0(sK1,sK0) = k5_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f302,f502])).

fof(f502,plain,
    ( sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f501,f39])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f501,plain,
    ( sK0 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK0))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f492,f37])).

% (12213)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f492,plain,
    ( k5_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,k1_xboole_0)))
    | ~ spl3_1 ),
    inference(superposition,[],[f326,f36])).

fof(f326,plain,
    ( ! [X0] : k5_xboole_0(sK0,k5_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,X0))))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f315,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f315,plain,
    ( ! [X0] : k5_xboole_0(k5_xboole_0(sK0,sK1),X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),X0)))
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f244,f281])).

fof(f281,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f53,f213])).

fof(f213,plain,(
    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f125,f54])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f38,f41,f41])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f244,plain,
    ( ! [X0] : k5_xboole_0(k4_xboole_0(sK0,sK1),X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK0,sK1),X0)))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f243,f52])).

fof(f243,plain,
    ( ! [X0] : k5_xboole_0(k4_xboole_0(sK0,sK1),X0) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)),X0))
    | ~ spl3_1 ),
    inference(superposition,[],[f52,f191])).

fof(f191,plain,
    ( k4_xboole_0(sK0,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f167,f165])).

fof(f165,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl3_1 ),
    inference(superposition,[],[f53,f126])).

fof(f126,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | ~ spl3_1 ),
    inference(superposition,[],[f115,f54])).

fof(f115,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f113,f55])).

fof(f113,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f61,f109])).

fof(f109,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f30,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f61,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_1
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f167,plain,
    ( k4_xboole_0(sK0,sK1) = k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | ~ spl3_1 ),
    inference(superposition,[],[f53,f126])).

fof(f302,plain,
    ( k5_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f179,f281])).

fof(f179,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f126,f165])).

fof(f343,plain,(
    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f283,f281])).

fof(f283,plain,(
    sK1 = k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f53,f213])).

fof(f105,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f96,f34])).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f96,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f76,f94])).

fof(f94,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f91,f36])).

fof(f91,plain,
    ( k4_xboole_0(sK0,sK0) = k5_xboole_0(sK0,sK0)
    | ~ spl3_2 ),
    inference(superposition,[],[f53,f87])).

fof(f87,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK0))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f78,f55])).

fof(f78,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f73,f57])).

fof(f73,plain,
    ( r2_hidden(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f33,f70,f42])).

fof(f70,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f30,f65])).

fof(f65,plain,
    ( sK0 = sK1
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f76,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK0),sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f71,f72])).

fof(f72,plain,
    ( k3_subset_1(sK0,sK0) = k4_xboole_0(sK0,sK0)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f70,f47])).

fof(f71,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f62,f65])).

fof(f62,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f69,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f68,f64,f60])).

fof(f68,plain,
    ( sK0 = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f31,f35])).

fof(f35,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f31,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f58,f64,f60])).

fof(f58,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f32,f35])).

fof(f32,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:56:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.50  % (12217)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.50  % (12233)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.51  % (12225)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.51  % (12217)Refutation not found, incomplete strategy% (12217)------------------------------
% 0.19/0.51  % (12217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (12217)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (12217)Memory used [KB]: 10618
% 0.19/0.51  % (12217)Time elapsed: 0.103 s
% 0.19/0.51  % (12217)------------------------------
% 0.19/0.51  % (12217)------------------------------
% 0.19/0.51  % (12220)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.52  % (12219)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (12221)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.52  % (12209)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.52  % (12207)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.52  % (12212)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.52  % (12211)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.53  % (12210)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.53  % (12231)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.54  % (12223)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.54  % (12227)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.54  % (12222)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.54  % (12226)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.54  % (12215)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.54  % (12224)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.54  % (12214)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.54  % (12229)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.54  % (12208)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.54  % (12230)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.54  % (12233)Refutation found. Thanks to Tanya!
% 0.19/0.54  % SZS status Theorem for theBenchmark
% 0.19/0.54  % (12234)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.54  % (12229)Refutation not found, incomplete strategy% (12229)------------------------------
% 0.19/0.54  % (12229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (12229)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (12229)Memory used [KB]: 10746
% 0.19/0.54  % (12229)Time elapsed: 0.104 s
% 0.19/0.54  % (12229)------------------------------
% 0.19/0.54  % (12229)------------------------------
% 0.19/0.54  % SZS output start Proof for theBenchmark
% 0.19/0.54  fof(f617,plain,(
% 0.19/0.54    $false),
% 0.19/0.54    inference(avatar_sat_refutation,[],[f67,f69,f105,f583])).
% 0.19/0.54  fof(f583,plain,(
% 0.19/0.54    ~spl3_1 | spl3_2),
% 0.19/0.54    inference(avatar_contradiction_clause,[],[f582])).
% 0.19/0.54  % (12216)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.54  fof(f582,plain,(
% 0.19/0.54    $false | (~spl3_1 | spl3_2)),
% 0.19/0.54    inference(subsumption_resolution,[],[f581,f66])).
% 0.19/0.54  fof(f66,plain,(
% 0.19/0.54    sK0 != sK1 | spl3_2),
% 0.19/0.54    inference(avatar_component_clause,[],[f64])).
% 0.19/0.54  fof(f64,plain,(
% 0.19/0.54    spl3_2 <=> sK0 = sK1),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.54  fof(f581,plain,(
% 0.19/0.54    sK0 = sK1 | ~spl3_1),
% 0.19/0.54    inference(forward_demodulation,[],[f548,f37])).
% 0.19/0.54  fof(f37,plain,(
% 0.19/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.54    inference(cnf_transformation,[],[f7])).
% 0.19/0.54  fof(f7,axiom,(
% 0.19/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.19/0.54  fof(f548,plain,(
% 0.19/0.54    sK1 = k5_xboole_0(sK0,k1_xboole_0) | ~spl3_1),
% 0.19/0.54    inference(backward_demodulation,[],[f343,f512])).
% 0.19/0.54  fof(f512,plain,(
% 0.19/0.54    k1_xboole_0 = k5_xboole_0(sK0,sK1) | ~spl3_1),
% 0.19/0.54    inference(forward_demodulation,[],[f505,f220])).
% 0.19/0.54  fof(f220,plain,(
% 0.19/0.54    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.19/0.54    inference(forward_demodulation,[],[f217,f36])).
% 0.19/0.54  fof(f36,plain,(
% 0.19/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f9])).
% 0.19/0.54  fof(f9,axiom,(
% 0.19/0.54    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.19/0.54  fof(f217,plain,(
% 0.19/0.54    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1)),
% 0.19/0.54    inference(superposition,[],[f53,f125])).
% 0.19/0.54  fof(f125,plain,(
% 0.19/0.54    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 0.19/0.54    inference(unit_resulting_resolution,[],[f116,f55])).
% 0.19/0.54  fof(f55,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 0.19/0.54    inference(definition_unfolding,[],[f46,f41])).
% 0.19/0.54  fof(f41,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.54    inference(cnf_transformation,[],[f6])).
% 0.19/0.54  fof(f6,axiom,(
% 0.19/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.54  fof(f46,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f19])).
% 0.19/0.54  fof(f19,plain,(
% 0.19/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.19/0.54    inference(ennf_transformation,[],[f4])).
% 0.19/0.54  fof(f4,axiom,(
% 0.19/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.19/0.54  fof(f116,plain,(
% 0.19/0.54    r1_tarski(sK1,sK0)),
% 0.19/0.54    inference(unit_resulting_resolution,[],[f110,f57])).
% 0.19/0.54  fof(f57,plain,(
% 0.19/0.54    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.19/0.54    inference(equality_resolution,[],[f48])).
% 0.19/0.54  fof(f48,plain,(
% 0.19/0.54    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.19/0.54    inference(cnf_transformation,[],[f29])).
% 0.19/0.54  fof(f29,plain,(
% 0.19/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 0.19/0.54  fof(f28,plain,(
% 0.19/0.54    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.19/0.54    introduced(choice_axiom,[])).
% 0.19/0.54  fof(f27,plain,(
% 0.19/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.54    inference(rectify,[],[f26])).
% 0.19/0.54  fof(f26,plain,(
% 0.19/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.54    inference(nnf_transformation,[],[f10])).
% 0.19/0.54  fof(f10,axiom,(
% 0.19/0.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.19/0.54  fof(f110,plain,(
% 0.19/0.54    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.54    inference(unit_resulting_resolution,[],[f33,f30,f42])).
% 0.19/0.54  fof(f42,plain,(
% 0.19/0.54    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f25])).
% 0.19/0.54  fof(f25,plain,(
% 0.19/0.54    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.19/0.54    inference(nnf_transformation,[],[f18])).
% 0.19/0.54  % (12216)Refutation not found, incomplete strategy% (12216)------------------------------
% 0.19/0.54  % (12216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (12216)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (12216)Memory used [KB]: 10618
% 0.19/0.54  % (12216)Time elapsed: 0.146 s
% 0.19/0.54  % (12216)------------------------------
% 0.19/0.54  % (12216)------------------------------
% 0.19/0.54  fof(f18,plain,(
% 0.19/0.54    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.19/0.54    inference(ennf_transformation,[],[f11])).
% 0.19/0.54  fof(f11,axiom,(
% 0.19/0.54    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.19/0.54  fof(f30,plain,(
% 0.19/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.54    inference(cnf_transformation,[],[f24])).
% 0.19/0.54  fof(f24,plain,(
% 0.19/0.54    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 0.19/0.55  fof(f23,plain,(
% 0.19/0.55    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.19/0.55    introduced(choice_axiom,[])).
% 0.19/0.55  fof(f22,plain,(
% 0.19/0.55    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.55    inference(flattening,[],[f21])).
% 0.19/0.55  fof(f21,plain,(
% 0.19/0.55    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.55    inference(nnf_transformation,[],[f17])).
% 0.19/0.55  fof(f17,plain,(
% 0.19/0.55    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.55    inference(ennf_transformation,[],[f16])).
% 0.19/0.55  fof(f16,negated_conjecture,(
% 0.19/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.19/0.55    inference(negated_conjecture,[],[f15])).
% 0.19/0.55  fof(f15,conjecture,(
% 0.19/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.19/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).
% 0.19/0.55  fof(f33,plain,(
% 0.19/0.55    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.19/0.55    inference(cnf_transformation,[],[f14])).
% 0.19/0.55  fof(f14,axiom,(
% 0.19/0.55    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.19/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.19/0.55  % (12236)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.55  fof(f53,plain,(
% 0.19/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.19/0.55    inference(definition_unfolding,[],[f40,f41])).
% 0.19/0.55  fof(f40,plain,(
% 0.19/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.19/0.55    inference(cnf_transformation,[],[f3])).
% 0.19/0.55  fof(f3,axiom,(
% 0.19/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.19/0.55  fof(f505,plain,(
% 0.19/0.55    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK0,sK1) | ~spl3_1),
% 0.19/0.55    inference(backward_demodulation,[],[f302,f502])).
% 0.19/0.55  fof(f502,plain,(
% 0.19/0.55    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | ~spl3_1),
% 0.19/0.55    inference(forward_demodulation,[],[f501,f39])).
% 0.19/0.55  fof(f39,plain,(
% 0.19/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f2])).
% 0.19/0.55  fof(f2,axiom,(
% 0.19/0.55    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.19/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.19/0.55  fof(f501,plain,(
% 0.19/0.55    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK0)) | ~spl3_1),
% 0.19/0.55    inference(forward_demodulation,[],[f492,f37])).
% 0.19/0.55  % (12213)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.55  fof(f492,plain,(
% 0.19/0.55    k5_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,k1_xboole_0))) | ~spl3_1),
% 0.19/0.55    inference(superposition,[],[f326,f36])).
% 0.19/0.55  fof(f326,plain,(
% 0.19/0.55    ( ! [X0] : (k5_xboole_0(sK0,k5_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,X0))))) ) | ~spl3_1),
% 0.19/0.55    inference(forward_demodulation,[],[f315,f52])).
% 0.19/0.55  fof(f52,plain,(
% 0.19/0.55    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.19/0.55    inference(cnf_transformation,[],[f8])).
% 0.19/0.55  fof(f8,axiom,(
% 0.19/0.55    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.19/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.19/0.55  fof(f315,plain,(
% 0.19/0.55    ( ! [X0] : (k5_xboole_0(k5_xboole_0(sK0,sK1),X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),X0)))) ) | ~spl3_1),
% 0.19/0.55    inference(backward_demodulation,[],[f244,f281])).
% 0.19/0.55  fof(f281,plain,(
% 0.19/0.55    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 0.19/0.55    inference(superposition,[],[f53,f213])).
% 0.19/0.55  fof(f213,plain,(
% 0.19/0.55    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.19/0.55    inference(superposition,[],[f125,f54])).
% 0.19/0.55  fof(f54,plain,(
% 0.19/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.19/0.55    inference(definition_unfolding,[],[f38,f41,f41])).
% 0.19/0.55  fof(f38,plain,(
% 0.19/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f1])).
% 0.19/0.55  fof(f1,axiom,(
% 0.19/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.55  fof(f244,plain,(
% 0.19/0.55    ( ! [X0] : (k5_xboole_0(k4_xboole_0(sK0,sK1),X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK0,sK1),X0)))) ) | ~spl3_1),
% 0.19/0.55    inference(forward_demodulation,[],[f243,f52])).
% 0.19/0.55  fof(f243,plain,(
% 0.19/0.55    ( ! [X0] : (k5_xboole_0(k4_xboole_0(sK0,sK1),X0) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)),X0))) ) | ~spl3_1),
% 0.19/0.55    inference(superposition,[],[f52,f191])).
% 0.19/0.55  fof(f191,plain,(
% 0.19/0.55    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | ~spl3_1),
% 0.19/0.55    inference(forward_demodulation,[],[f167,f165])).
% 0.19/0.55  fof(f165,plain,(
% 0.19/0.55    k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~spl3_1),
% 0.19/0.55    inference(superposition,[],[f53,f126])).
% 0.19/0.55  fof(f126,plain,(
% 0.19/0.55    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | ~spl3_1),
% 0.19/0.55    inference(superposition,[],[f115,f54])).
% 0.19/0.55  fof(f115,plain,(
% 0.19/0.55    k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) | ~spl3_1),
% 0.19/0.55    inference(unit_resulting_resolution,[],[f113,f55])).
% 0.19/0.55  fof(f113,plain,(
% 0.19/0.55    r1_tarski(k4_xboole_0(sK0,sK1),sK1) | ~spl3_1),
% 0.19/0.55    inference(backward_demodulation,[],[f61,f109])).
% 0.19/0.55  fof(f109,plain,(
% 0.19/0.55    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.19/0.55    inference(unit_resulting_resolution,[],[f30,f47])).
% 0.19/0.55  fof(f47,plain,(
% 0.19/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.55    inference(cnf_transformation,[],[f20])).
% 0.19/0.55  fof(f20,plain,(
% 0.19/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.55    inference(ennf_transformation,[],[f13])).
% 0.19/0.55  fof(f13,axiom,(
% 0.19/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.19/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.19/0.55  fof(f61,plain,(
% 0.19/0.55    r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl3_1),
% 0.19/0.55    inference(avatar_component_clause,[],[f60])).
% 0.19/0.55  fof(f60,plain,(
% 0.19/0.55    spl3_1 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.19/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.55  fof(f167,plain,(
% 0.19/0.55    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | ~spl3_1),
% 0.19/0.55    inference(superposition,[],[f53,f126])).
% 0.19/0.55  fof(f302,plain,(
% 0.19/0.55    k5_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | ~spl3_1),
% 0.19/0.55    inference(backward_demodulation,[],[f179,f281])).
% 0.19/0.55  fof(f179,plain,(
% 0.19/0.55    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | ~spl3_1),
% 0.19/0.55    inference(backward_demodulation,[],[f126,f165])).
% 0.19/0.55  fof(f343,plain,(
% 0.19/0.55    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 0.19/0.55    inference(forward_demodulation,[],[f283,f281])).
% 0.19/0.55  fof(f283,plain,(
% 0.19/0.55    sK1 = k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.19/0.55    inference(superposition,[],[f53,f213])).
% 0.19/0.55  fof(f105,plain,(
% 0.19/0.55    spl3_1 | ~spl3_2),
% 0.19/0.55    inference(avatar_contradiction_clause,[],[f104])).
% 0.19/0.55  fof(f104,plain,(
% 0.19/0.55    $false | (spl3_1 | ~spl3_2)),
% 0.19/0.55    inference(subsumption_resolution,[],[f96,f34])).
% 0.19/0.55  fof(f34,plain,(
% 0.19/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f5])).
% 0.19/0.55  fof(f5,axiom,(
% 0.19/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.19/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.19/0.55  fof(f96,plain,(
% 0.19/0.55    ~r1_tarski(k1_xboole_0,sK0) | (spl3_1 | ~spl3_2)),
% 0.19/0.55    inference(backward_demodulation,[],[f76,f94])).
% 0.19/0.55  fof(f94,plain,(
% 0.19/0.55    k1_xboole_0 = k4_xboole_0(sK0,sK0) | ~spl3_2),
% 0.19/0.55    inference(forward_demodulation,[],[f91,f36])).
% 0.19/0.55  fof(f91,plain,(
% 0.19/0.55    k4_xboole_0(sK0,sK0) = k5_xboole_0(sK0,sK0) | ~spl3_2),
% 0.19/0.55    inference(superposition,[],[f53,f87])).
% 0.19/0.55  fof(f87,plain,(
% 0.19/0.55    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)) | ~spl3_2),
% 0.19/0.55    inference(unit_resulting_resolution,[],[f78,f55])).
% 0.19/0.55  fof(f78,plain,(
% 0.19/0.55    r1_tarski(sK0,sK0) | ~spl3_2),
% 0.19/0.55    inference(unit_resulting_resolution,[],[f73,f57])).
% 0.19/0.55  fof(f73,plain,(
% 0.19/0.55    r2_hidden(sK0,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.19/0.55    inference(unit_resulting_resolution,[],[f33,f70,f42])).
% 0.19/0.55  fof(f70,plain,(
% 0.19/0.55    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.19/0.55    inference(backward_demodulation,[],[f30,f65])).
% 0.19/0.55  fof(f65,plain,(
% 0.19/0.55    sK0 = sK1 | ~spl3_2),
% 0.19/0.55    inference(avatar_component_clause,[],[f64])).
% 0.19/0.55  fof(f76,plain,(
% 0.19/0.55    ~r1_tarski(k4_xboole_0(sK0,sK0),sK0) | (spl3_1 | ~spl3_2)),
% 0.19/0.55    inference(backward_demodulation,[],[f71,f72])).
% 0.19/0.55  fof(f72,plain,(
% 0.19/0.55    k3_subset_1(sK0,sK0) = k4_xboole_0(sK0,sK0) | ~spl3_2),
% 0.19/0.55    inference(unit_resulting_resolution,[],[f70,f47])).
% 0.19/0.55  fof(f71,plain,(
% 0.19/0.55    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | (spl3_1 | ~spl3_2)),
% 0.19/0.55    inference(forward_demodulation,[],[f62,f65])).
% 0.19/0.55  fof(f62,plain,(
% 0.19/0.55    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | spl3_1),
% 0.19/0.55    inference(avatar_component_clause,[],[f60])).
% 0.19/0.55  fof(f69,plain,(
% 0.19/0.55    spl3_1 | spl3_2),
% 0.19/0.55    inference(avatar_split_clause,[],[f68,f64,f60])).
% 0.19/0.55  fof(f68,plain,(
% 0.19/0.55    sK0 = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.19/0.55    inference(forward_demodulation,[],[f31,f35])).
% 0.19/0.55  fof(f35,plain,(
% 0.19/0.55    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.19/0.55    inference(cnf_transformation,[],[f12])).
% 0.19/0.55  fof(f12,axiom,(
% 0.19/0.55    ! [X0] : k2_subset_1(X0) = X0),
% 0.19/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.19/0.55  fof(f31,plain,(
% 0.19/0.55    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.19/0.55    inference(cnf_transformation,[],[f24])).
% 0.19/0.55  fof(f67,plain,(
% 0.19/0.55    ~spl3_1 | ~spl3_2),
% 0.19/0.55    inference(avatar_split_clause,[],[f58,f64,f60])).
% 0.19/0.55  fof(f58,plain,(
% 0.19/0.55    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.19/0.55    inference(forward_demodulation,[],[f32,f35])).
% 0.19/0.55  fof(f32,plain,(
% 0.19/0.55    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.19/0.55    inference(cnf_transformation,[],[f24])).
% 0.19/0.55  % SZS output end Proof for theBenchmark
% 0.19/0.55  % (12233)------------------------------
% 0.19/0.55  % (12233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (12233)Termination reason: Refutation
% 0.19/0.55  
% 0.19/0.55  % (12233)Memory used [KB]: 11001
% 0.19/0.55  % (12233)Time elapsed: 0.147 s
% 0.19/0.55  % (12233)------------------------------
% 0.19/0.55  % (12233)------------------------------
% 0.19/0.55  % (12218)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.55  % (12218)Refutation not found, incomplete strategy% (12218)------------------------------
% 0.19/0.55  % (12218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (12218)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (12218)Memory used [KB]: 10618
% 0.19/0.55  % (12218)Time elapsed: 0.142 s
% 0.19/0.55  % (12218)------------------------------
% 0.19/0.55  % (12218)------------------------------
% 0.19/0.55  % (12206)Success in time 0.191 s
%------------------------------------------------------------------------------
