%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 139 expanded)
%              Number of leaves         :   22 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :  239 ( 351 expanded)
%              Number of equality atoms :   53 (  99 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f168,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f63,f77,f80,f116,f118,f126,f143,f149,f167])).

fof(f167,plain,
    ( ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(resolution,[],[f158,f76])).

fof(f76,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_4
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f158,plain,
    ( ! [X0] : r2_hidden(sK0,X0)
    | ~ spl3_7 ),
    inference(trivial_inequality_removal,[],[f157])).

fof(f157,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | r2_hidden(sK0,X0) )
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f152,f64])).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f37,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f152,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0)
        | r2_hidden(sK0,X0) )
    | ~ spl3_7 ),
    inference(superposition,[],[f120,f138])).

fof(f138,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl3_7
  <=> k1_xboole_0 = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) != k3_xboole_0(k2_tarski(X1,X1),X0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f51,f37])).

% (31517)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% (31513)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% (31526)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% (31516)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% (31525)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% (31522)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% (31528)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% (31518)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% (31522)Refutation not found, incomplete strategy% (31522)------------------------------
% (31522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31522)Termination reason: Refutation not found, incomplete strategy

% (31522)Memory used [KB]: 10618
% (31522)Time elapsed: 0.058 s
% (31522)------------------------------
% (31522)------------------------------
% (31511)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% (31520)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% (31523)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f51,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) != k3_xboole_0(X0,k2_tarski(X1,X1))
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f45,f36,f36])).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

fof(f149,plain,
    ( ~ spl3_1
    | spl3_8 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | ~ spl3_1
    | spl3_8 ),
    inference(resolution,[],[f144,f56])).

fof(f56,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_1
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f144,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl3_8 ),
    inference(resolution,[],[f142,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f36])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f142,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK0),k2_relat_1(sK1))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl3_8
  <=> r1_tarski(k2_tarski(sK0,sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f143,plain,
    ( ~ spl3_5
    | spl3_7
    | ~ spl3_8
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f132,f59,f140,f136,f109])).

fof(f109,plain,
    ( spl3_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f59,plain,
    ( spl3_2
  <=> k1_xboole_0 = k10_relat_1(sK1,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f132,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK0),k2_relat_1(sK1))
    | k1_xboole_0 = k2_tarski(sK0,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f131])).

fof(f131,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k2_tarski(sK0,sK0),k2_relat_1(sK1))
    | k1_xboole_0 = k2_tarski(sK0,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(superposition,[],[f42,f61])).

fof(f61,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k2_tarski(sK0,sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

fof(f126,plain,
    ( spl3_1
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl3_1
    | spl3_6 ),
    inference(resolution,[],[f123,f57])).

fof(f57,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f123,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | spl3_6 ),
    inference(resolution,[],[f119,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f36])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f119,plain,
    ( ~ r1_xboole_0(k2_tarski(sK0,sK0),k2_relat_1(sK1))
    | spl3_6 ),
    inference(resolution,[],[f115,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f115,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),k2_tarski(sK0,sK0))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl3_6
  <=> r1_xboole_0(k2_relat_1(sK1),k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f118,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f111,f31])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
      | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
    & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
      | r2_hidden(sK0,k2_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).

fof(f25,plain,
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

fof(f24,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(f111,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f116,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | spl3_2 ),
    inference(avatar_split_clause,[],[f107,f59,f113,f109])).

fof(f107,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),k2_tarski(sK0,sK0))
    | ~ v1_relat_1(sK1)
    | spl3_2 ),
    inference(trivial_inequality_removal,[],[f104])).

fof(f104,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(sK1),k2_tarski(sK0,sK0))
    | ~ v1_relat_1(sK1)
    | spl3_2 ),
    inference(superposition,[],[f60,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f60,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k2_tarski(sK0,sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f80,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | ~ spl3_3 ),
    inference(resolution,[],[f73,f34])).

fof(f34,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f73,plain,
    ( ! [X0] : ~ r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_3
  <=> ! [X0] : ~ r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f77,plain,
    ( spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f68,f75,f72])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f39,f35])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f63,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f49,f59,f55])).

fof(f49,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k2_tarski(sK0,sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f32,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f48,f59,f55])).

fof(f48,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k2_tarski(sK0,sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f33,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:13:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (31515)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (31514)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (31515)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f168,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f62,f63,f77,f80,f116,f118,f126,f143,f149,f167])).
% 0.21/0.47  fof(f167,plain,(
% 0.21/0.47    ~spl3_4 | ~spl3_7),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f166])).
% 0.21/0.47  fof(f166,plain,(
% 0.21/0.47    $false | (~spl3_4 | ~spl3_7)),
% 0.21/0.47    inference(resolution,[],[f158,f76])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f75])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    spl3_4 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK0,X0)) ) | ~spl3_7),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f157])).
% 0.21/0.47  fof(f157,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r2_hidden(sK0,X0)) ) | ~spl3_7),
% 0.21/0.47    inference(forward_demodulation,[],[f152,f64])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(superposition,[],[f37,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0) | r2_hidden(sK0,X0)) ) | ~spl3_7),
% 0.21/0.47    inference(superposition,[],[f120,f138])).
% 0.21/0.47  fof(f138,plain,(
% 0.21/0.47    k1_xboole_0 = k2_tarski(sK0,sK0) | ~spl3_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f136])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    spl3_7 <=> k1_xboole_0 = k2_tarski(sK0,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X1,X1) != k3_xboole_0(k2_tarski(X1,X1),X0) | r2_hidden(X1,X0)) )),
% 0.21/0.47    inference(superposition,[],[f51,f37])).
% 0.21/0.47  % (31517)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (31513)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (31526)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (31516)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (31525)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (31522)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (31528)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (31518)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (31522)Refutation not found, incomplete strategy% (31522)------------------------------
% 0.21/0.48  % (31522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31522)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (31522)Memory used [KB]: 10618
% 0.21/0.48  % (31522)Time elapsed: 0.058 s
% 0.21/0.48  % (31522)------------------------------
% 0.21/0.48  % (31522)------------------------------
% 0.21/0.48  % (31511)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (31520)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (31523)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tarski(X1,X1) != k3_xboole_0(X0,k2_tarski(X1,X1)) | r2_hidden(X1,X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f45,f36,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    ~spl3_1 | spl3_8),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f148])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    $false | (~spl3_1 | spl3_8)),
% 0.21/0.49    inference(resolution,[],[f144,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_relat_1(sK1)) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    spl3_1 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k2_relat_1(sK1)) | spl3_8),
% 0.21/0.49    inference(resolution,[],[f142,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f47,f36])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    ~r1_tarski(k2_tarski(sK0,sK0),k2_relat_1(sK1)) | spl3_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f140])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    spl3_8 <=> r1_tarski(k2_tarski(sK0,sK0),k2_relat_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    ~spl3_5 | spl3_7 | ~spl3_8 | ~spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f132,f59,f140,f136,f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    spl3_5 <=> v1_relat_1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl3_2 <=> k1_xboole_0 = k10_relat_1(sK1,k2_tarski(sK0,sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ~r1_tarski(k2_tarski(sK0,sK0),k2_relat_1(sK1)) | k1_xboole_0 = k2_tarski(sK0,sK0) | ~v1_relat_1(sK1) | ~spl3_2),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f131])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k2_tarski(sK0,sK0),k2_relat_1(sK1)) | k1_xboole_0 = k2_tarski(sK0,sK0) | ~v1_relat_1(sK1) | ~spl3_2),
% 0.21/0.49    inference(superposition,[],[f42,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    k1_xboole_0 = k10_relat_1(sK1,k2_tarski(sK0,sK0)) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f59])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    spl3_1 | spl3_6),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f125])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    $false | (spl3_1 | spl3_6)),
% 0.21/0.49    inference(resolution,[],[f123,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k2_relat_1(sK1)) | spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f55])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_relat_1(sK1)) | spl3_6),
% 0.21/0.49    inference(resolution,[],[f119,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f43,f36])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    ~r1_xboole_0(k2_tarski(sK0,sK0),k2_relat_1(sK1)) | spl3_6),
% 0.21/0.49    inference(resolution,[],[f115,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    ~r1_xboole_0(k2_relat_1(sK1),k2_tarski(sK0,sK0)) | spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f113])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    spl3_6 <=> r1_xboole_0(k2_relat_1(sK1),k2_tarski(sK0,sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    spl3_5),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f117])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    $false | spl3_5),
% 0.21/0.49    inference(resolution,[],[f111,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    (k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ? [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1)))) & v1_relat_1(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) & v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.21/0.49    inference(negated_conjecture,[],[f12])).
% 0.21/0.49  fof(f12,conjecture,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ~v1_relat_1(sK1) | spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f109])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    ~spl3_5 | ~spl3_6 | spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f107,f59,f113,f109])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    ~r1_xboole_0(k2_relat_1(sK1),k2_tarski(sK0,sK0)) | ~v1_relat_1(sK1) | spl3_2),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f104])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k2_relat_1(sK1),k2_tarski(sK0,sK0)) | ~v1_relat_1(sK1) | spl3_2),
% 0.21/0.49    inference(superposition,[],[f60,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    k1_xboole_0 != k10_relat_1(sK1,k2_tarski(sK0,sK0)) | spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f59])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ~spl3_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    $false | ~spl3_3),
% 0.21/0.49    inference(resolution,[],[f73,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl3_3 <=> ! [X0] : ~r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl3_3 | spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f68,f75,f72])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(superposition,[],[f39,f35])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(rectify,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl3_1 | ~spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f49,f59,f55])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    k1_xboole_0 != k10_relat_1(sK1,k2_tarski(sK0,sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.49    inference(definition_unfolding,[],[f32,f36])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ~spl3_1 | spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f48,f59,f55])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    k1_xboole_0 = k10_relat_1(sK1,k2_tarski(sK0,sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.49    inference(definition_unfolding,[],[f33,f36])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (31515)------------------------------
% 0.21/0.49  % (31515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (31515)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (31515)Memory used [KB]: 6140
% 0.21/0.49  % (31515)Time elapsed: 0.056 s
% 0.21/0.49  % (31515)------------------------------
% 0.21/0.49  % (31515)------------------------------
% 0.21/0.49  % (31510)Success in time 0.131 s
%------------------------------------------------------------------------------
