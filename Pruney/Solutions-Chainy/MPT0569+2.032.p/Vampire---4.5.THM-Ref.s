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
% DateTime   : Thu Dec  3 12:50:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 226 expanded)
%              Number of leaves         :   14 (  66 expanded)
%              Depth                    :   14
%              Number of atoms          :  199 ( 615 expanded)
%              Number of equality atoms :   43 ( 118 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f444,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f76,f113,f117,f275,f443])).

fof(f443,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | ~ spl7_1
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f42,f432,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f432,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl7_1
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f408,f408,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f408,plain,
    ( r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),k1_xboole_0)
    | ~ spl7_1
    | spl7_2 ),
    inference(forward_demodulation,[],[f402,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl7_1
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f402,plain,
    ( r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),k10_relat_1(sK1,sK0))
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f24,f309,f308,f361,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f361,plain,
    ( r2_hidden(k4_tarski(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),sK2(k2_relat_1(sK1),sK0)),sK1)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f308,f48])).

% (17805)Refutation not found, incomplete strategy% (17805)------------------------------
% (17805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f48,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK5(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

% (17805)Termination reason: Refutation not found, incomplete strategy

% (17805)Memory used [KB]: 10746
% (17805)Time elapsed: 0.161 s
% (17805)------------------------------
% (17805)------------------------------
fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f308,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f63,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl7_2
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f309,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),sK0),sK0)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f63,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f42,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f275,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f51,f219])).

fof(f219,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f121,f212])).

fof(f212,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(superposition,[],[f146,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f146,plain,
    ( ! [X0] : k10_relat_1(sK1,k1_xboole_0) = k4_xboole_0(k10_relat_1(sK1,k1_xboole_0),X0)
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f131,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f5])).

% (17809)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f131,plain,
    ( ! [X0] : r1_xboole_0(k10_relat_1(sK1,k1_xboole_0),X0)
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f127,f28])).

fof(f127,plain,
    ( ! [X0] : ~ r2_hidden(X0,k10_relat_1(sK1,k1_xboole_0))
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f112,f120])).

fof(f120,plain,
    ( k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f118,f119])).

fof(f119,plain,(
    k10_relat_1(sK1,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))) = k10_relat_1(sK1,k1_xboole_0) ),
    inference(superposition,[],[f52,f42])).

fof(f52,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),X0))) ),
    inference(unit_resulting_resolution,[],[f24,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f38,f44])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f118,plain,
    ( k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)))
    | ~ spl7_2 ),
    inference(superposition,[],[f52,f66])).

fof(f66,plain,
    ( k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f64,f26])).

fof(f64,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f112,plain,
    ( ! [X0] : ~ r2_hidden(X0,k10_relat_1(sK1,sK0))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl7_4
  <=> ! [X0] : ~ r2_hidden(X0,k10_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f121,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k10_relat_1(sK1,k1_xboole_0),k10_relat_1(sK1,k1_xboole_0))
    | spl7_1
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f79,f120])).

fof(f79,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k10_relat_1(sK1,sK0),k10_relat_1(sK1,sK0))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f59,f59,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f59,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f51,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f117,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f24,f109])).

fof(f109,plain,
    ( ~ v1_relat_1(sK1)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl7_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f113,plain,
    ( ~ spl7_3
    | spl7_4
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f105,f62,f111,f107])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k10_relat_1(sK1,sK0))
        | ~ v1_relat_1(sK1) )
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k10_relat_1(sK1,sK0))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k10_relat_1(sK1,sK0)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f100,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(X0,sK0,sK1),k2_relat_1(sK1))
        | ~ r2_hidden(X0,k10_relat_1(sK1,sK0)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f55,f67])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f64,f27])).

fof(f55,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK3(X3,X4,sK1),X4)
      | ~ r2_hidden(X3,k10_relat_1(sK1,X4)) ) ),
    inference(resolution,[],[f24,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f76,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f23,f62,f58])).

fof(f23,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 != k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f65,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f22,f62,f58])).

fof(f22,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:51:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (17806)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (17800)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (17798)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.56  % (17815)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (17796)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (17798)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.57  % (17799)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.57  % (17794)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.57  % (17813)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.58  % (17808)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.58  % (17817)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.58  % (17805)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f444,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(avatar_sat_refutation,[],[f65,f76,f113,f117,f275,f443])).
% 0.22/0.58  fof(f443,plain,(
% 0.22/0.58    ~spl7_1 | spl7_2),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f442])).
% 0.22/0.58  fof(f442,plain,(
% 0.22/0.58    $false | (~spl7_1 | spl7_2)),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f42,f432,f25])).
% 0.22/0.58  fof(f25,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.58  fof(f432,plain,(
% 0.22/0.58    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl7_1 | spl7_2)),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f408,f408,f27])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  fof(f19,plain,(
% 0.22/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.58    inference(ennf_transformation,[],[f17])).
% 0.22/0.59  fof(f17,plain,(
% 0.22/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.59    inference(rectify,[],[f1])).
% 0.22/0.59  fof(f1,axiom,(
% 0.22/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.59  fof(f408,plain,(
% 0.22/0.59    r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),k1_xboole_0) | (~spl7_1 | spl7_2)),
% 0.22/0.59    inference(forward_demodulation,[],[f402,f60])).
% 0.22/0.59  fof(f60,plain,(
% 0.22/0.59    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl7_1),
% 0.22/0.59    inference(avatar_component_clause,[],[f58])).
% 0.22/0.59  fof(f58,plain,(
% 0.22/0.59    spl7_1 <=> k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.59  fof(f402,plain,(
% 0.22/0.59    r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),k10_relat_1(sK1,sK0)) | spl7_2),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f24,f309,f308,f361,f33])).
% 0.22/0.59  fof(f33,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f20])).
% 0.22/0.59  fof(f20,plain,(
% 0.22/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.59    inference(ennf_transformation,[],[f13])).
% 0.22/0.59  fof(f13,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.22/0.59  fof(f361,plain,(
% 0.22/0.59    r2_hidden(k4_tarski(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),sK2(k2_relat_1(sK1),sK0)),sK1) | spl7_2),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f308,f48])).
% 0.22/0.59  % (17805)Refutation not found, incomplete strategy% (17805)------------------------------
% 0.22/0.59  % (17805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  fof(f48,plain,(
% 0.22/0.59    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK5(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.22/0.59    inference(equality_resolution,[],[f35])).
% 0.22/0.59  % (17805)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (17805)Memory used [KB]: 10746
% 0.22/0.59  % (17805)Time elapsed: 0.161 s
% 0.22/0.59  % (17805)------------------------------
% 0.22/0.59  % (17805)------------------------------
% 0.22/0.59  fof(f35,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.59    inference(cnf_transformation,[],[f12])).
% 0.22/0.59  fof(f12,axiom,(
% 0.22/0.59    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.22/0.59  fof(f308,plain,(
% 0.22/0.59    r2_hidden(sK2(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) | spl7_2),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f63,f28])).
% 0.22/0.59  fof(f28,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f19])).
% 0.22/0.59  fof(f63,plain,(
% 0.22/0.59    ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl7_2),
% 0.22/0.59    inference(avatar_component_clause,[],[f62])).
% 0.22/0.59  fof(f62,plain,(
% 0.22/0.59    spl7_2 <=> r1_xboole_0(k2_relat_1(sK1),sK0)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.59  fof(f309,plain,(
% 0.22/0.59    r2_hidden(sK2(k2_relat_1(sK1),sK0),sK0) | spl7_2),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f63,f29])).
% 0.22/0.59  fof(f29,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f19])).
% 0.22/0.59  fof(f24,plain,(
% 0.22/0.59    v1_relat_1(sK1)),
% 0.22/0.59    inference(cnf_transformation,[],[f18])).
% 0.22/0.59  fof(f18,plain,(
% 0.22/0.59    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.22/0.59    inference(ennf_transformation,[],[f16])).
% 0.22/0.59  fof(f16,negated_conjecture,(
% 0.22/0.59    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.59    inference(negated_conjecture,[],[f15])).
% 0.22/0.59  fof(f15,conjecture,(
% 0.22/0.59    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 0.22/0.59  fof(f42,plain,(
% 0.22/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f3])).
% 0.22/0.59  fof(f3,axiom,(
% 0.22/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.59  fof(f275,plain,(
% 0.22/0.59    spl7_1 | ~spl7_2 | ~spl7_4),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f260])).
% 0.22/0.59  fof(f260,plain,(
% 0.22/0.59    $false | (spl7_1 | ~spl7_2 | ~spl7_4)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f51,f219])).
% 0.22/0.59  fof(f219,plain,(
% 0.22/0.59    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | (spl7_1 | ~spl7_2 | ~spl7_4)),
% 0.22/0.59    inference(backward_demodulation,[],[f121,f212])).
% 0.22/0.59  fof(f212,plain,(
% 0.22/0.59    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) | (~spl7_2 | ~spl7_4)),
% 0.22/0.59    inference(superposition,[],[f146,f47])).
% 0.22/0.59  fof(f47,plain,(
% 0.22/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.59    inference(definition_unfolding,[],[f43,f44])).
% 0.22/0.59  fof(f44,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f4])).
% 0.22/0.59  fof(f4,axiom,(
% 0.22/0.59    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.59  fof(f43,plain,(
% 0.22/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f2])).
% 0.22/0.59  fof(f2,axiom,(
% 0.22/0.59    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.59  fof(f146,plain,(
% 0.22/0.59    ( ! [X0] : (k10_relat_1(sK1,k1_xboole_0) = k4_xboole_0(k10_relat_1(sK1,k1_xboole_0),X0)) ) | (~spl7_2 | ~spl7_4)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f131,f26])).
% 0.22/0.59  fof(f26,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f5])).
% 0.22/0.59  % (17809)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.59  fof(f131,plain,(
% 0.22/0.59    ( ! [X0] : (r1_xboole_0(k10_relat_1(sK1,k1_xboole_0),X0)) ) | (~spl7_2 | ~spl7_4)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f127,f28])).
% 0.22/0.59  fof(f127,plain,(
% 0.22/0.59    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK1,k1_xboole_0))) ) | (~spl7_2 | ~spl7_4)),
% 0.22/0.59    inference(backward_demodulation,[],[f112,f120])).
% 0.22/0.59  fof(f120,plain,(
% 0.22/0.59    k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0) | ~spl7_2),
% 0.22/0.59    inference(backward_demodulation,[],[f118,f119])).
% 0.22/0.59  fof(f119,plain,(
% 0.22/0.59    k10_relat_1(sK1,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))) = k10_relat_1(sK1,k1_xboole_0)),
% 0.22/0.59    inference(superposition,[],[f52,f42])).
% 0.22/0.59  fof(f52,plain,(
% 0.22/0.59    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),X0)))) )),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f24,f46])).
% 0.22/0.59  fof(f46,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)))) )),
% 0.22/0.59    inference(definition_unfolding,[],[f38,f44])).
% 0.22/0.59  fof(f38,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f21])).
% 0.22/0.59  fof(f21,plain,(
% 0.22/0.59    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.59    inference(ennf_transformation,[],[f14])).
% 0.22/0.59  fof(f14,axiom,(
% 0.22/0.59    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 0.22/0.59  fof(f118,plain,(
% 0.22/0.59    k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))) | ~spl7_2),
% 0.22/0.59    inference(superposition,[],[f52,f66])).
% 0.22/0.59  fof(f66,plain,(
% 0.22/0.59    k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),sK0) | ~spl7_2),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f64,f26])).
% 0.22/0.59  fof(f64,plain,(
% 0.22/0.59    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl7_2),
% 0.22/0.59    inference(avatar_component_clause,[],[f62])).
% 0.22/0.59  fof(f112,plain,(
% 0.22/0.59    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK1,sK0))) ) | ~spl7_4),
% 0.22/0.59    inference(avatar_component_clause,[],[f111])).
% 0.22/0.59  fof(f111,plain,(
% 0.22/0.59    spl7_4 <=> ! [X0] : ~r2_hidden(X0,k10_relat_1(sK1,sK0))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.59  fof(f121,plain,(
% 0.22/0.59    k1_xboole_0 != k2_zfmisc_1(k10_relat_1(sK1,k1_xboole_0),k10_relat_1(sK1,k1_xboole_0)) | (spl7_1 | ~spl7_2)),
% 0.22/0.59    inference(backward_demodulation,[],[f79,f120])).
% 0.22/0.59  fof(f79,plain,(
% 0.22/0.59    k1_xboole_0 != k2_zfmisc_1(k10_relat_1(sK1,sK0),k10_relat_1(sK1,sK0)) | spl7_1),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f59,f59,f39])).
% 0.22/0.59  fof(f39,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f9])).
% 0.22/0.59  fof(f9,axiom,(
% 0.22/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.59  fof(f59,plain,(
% 0.22/0.59    k1_xboole_0 != k10_relat_1(sK1,sK0) | spl7_1),
% 0.22/0.59    inference(avatar_component_clause,[],[f58])).
% 0.22/0.59  fof(f51,plain,(
% 0.22/0.59    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.59    inference(equality_resolution,[],[f40])).
% 0.22/0.59  fof(f40,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f9])).
% 0.22/0.59  fof(f117,plain,(
% 0.22/0.59    spl7_3),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f114])).
% 0.22/0.59  fof(f114,plain,(
% 0.22/0.59    $false | spl7_3),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f24,f109])).
% 0.22/0.59  fof(f109,plain,(
% 0.22/0.59    ~v1_relat_1(sK1) | spl7_3),
% 0.22/0.59    inference(avatar_component_clause,[],[f107])).
% 0.22/0.59  fof(f107,plain,(
% 0.22/0.59    spl7_3 <=> v1_relat_1(sK1)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.59  fof(f113,plain,(
% 0.22/0.59    ~spl7_3 | spl7_4 | ~spl7_2),
% 0.22/0.59    inference(avatar_split_clause,[],[f105,f62,f111,f107])).
% 0.22/0.59  fof(f105,plain,(
% 0.22/0.59    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)) ) | ~spl7_2),
% 0.22/0.59    inference(duplicate_literal_removal,[],[f103])).
% 0.22/0.59  fof(f103,plain,(
% 0.22/0.59    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k10_relat_1(sK1,sK0))) ) | ~spl7_2),
% 0.22/0.59    inference(resolution,[],[f100,f30])).
% 0.22/0.59  fof(f30,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f20])).
% 0.22/0.59  fof(f100,plain,(
% 0.22/0.59    ( ! [X0] : (~r2_hidden(sK3(X0,sK0,sK1),k2_relat_1(sK1)) | ~r2_hidden(X0,k10_relat_1(sK1,sK0))) ) | ~spl7_2),
% 0.22/0.59    inference(resolution,[],[f55,f67])).
% 0.22/0.59  fof(f67,plain,(
% 0.22/0.59    ( ! [X0] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl7_2),
% 0.22/0.59    inference(resolution,[],[f64,f27])).
% 0.22/0.59  fof(f55,plain,(
% 0.22/0.59    ( ! [X4,X3] : (r2_hidden(sK3(X3,X4,sK1),X4) | ~r2_hidden(X3,k10_relat_1(sK1,X4))) )),
% 0.22/0.59    inference(resolution,[],[f24,f32])).
% 0.22/0.59  fof(f32,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f20])).
% 0.22/0.59  fof(f76,plain,(
% 0.22/0.59    ~spl7_1 | ~spl7_2),
% 0.22/0.59    inference(avatar_split_clause,[],[f23,f62,f58])).
% 0.22/0.59  fof(f23,plain,(
% 0.22/0.59    ~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f18])).
% 0.22/0.59  fof(f65,plain,(
% 0.22/0.59    spl7_1 | spl7_2),
% 0.22/0.59    inference(avatar_split_clause,[],[f22,f62,f58])).
% 0.22/0.59  fof(f22,plain,(
% 0.22/0.59    r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f18])).
% 0.22/0.59  % SZS output end Proof for theBenchmark
% 0.22/0.59  % (17798)------------------------------
% 0.22/0.59  % (17798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (17798)Termination reason: Refutation
% 0.22/0.59  
% 0.22/0.59  % (17798)Memory used [KB]: 6396
% 0.22/0.59  % (17798)Time elapsed: 0.142 s
% 0.22/0.59  % (17798)------------------------------
% 0.22/0.59  % (17798)------------------------------
% 0.22/0.59  % (17793)Success in time 0.226 s
%------------------------------------------------------------------------------
