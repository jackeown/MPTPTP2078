%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 147 expanded)
%              Number of leaves         :   15 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  227 ( 405 expanded)
%              Number of equality atoms :   43 (  66 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f410,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f59,f123,f151,f195,f231,f404,f409])).

fof(f409,plain,
    ( spl4_3
    | spl4_14 ),
    inference(avatar_contradiction_clause,[],[f408])).

fof(f408,plain,
    ( $false
    | spl4_3
    | spl4_14 ),
    inference(subsumption_resolution,[],[f405,f57])).

fof(f57,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl4_3
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f405,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl4_14 ),
    inference(resolution,[],[f403,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f403,plain,
    ( ~ r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_relat_1(sK1))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f401])).

fof(f401,plain,
    ( spl4_14
  <=> r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f404,plain,
    ( ~ spl4_14
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f311,f120,f56,f52,f41,f401])).

fof(f41,plain,
    ( spl4_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f52,plain,
    ( spl4_2
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f120,plain,
    ( spl4_9
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f311,plain,
    ( ~ r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_relat_1(sK1))
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_9 ),
    inference(resolution,[],[f238,f57])).

fof(f238,plain,
    ( ! [X0] :
        ( r1_xboole_0(X0,sK0)
        | ~ r2_hidden(sK3(X0,sK0),k1_relat_1(sK1)) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(resolution,[],[f234,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f234,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(X1,k1_relat_1(sK1)) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f233,f136])).

fof(f136,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_9 ),
    inference(superposition,[],[f106,f122])).

fof(f122,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_xboole_0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f106,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,k1_xboole_0)))
    | ~ spl4_1 ),
    inference(superposition,[],[f91,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f91,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,k2_zfmisc_1(X0,X1))))
    | ~ spl4_1 ),
    inference(resolution,[],[f45,f27])).

fof(f27,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f45,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1))) )
    | ~ spl4_1 ),
    inference(resolution,[],[f43,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f43,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f233,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k1_xboole_0)
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ r2_hidden(X1,sK0) )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f212,f22])).

fof(f22,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f212,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k1_relat_1(k1_xboole_0))
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ r2_hidden(X1,sK0) )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f47,f54])).

fof(f54,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f47,plain,
    ( ! [X4,X5] :
        ( r2_hidden(X4,k1_relat_1(k7_relat_1(sK1,X5)))
        | ~ r2_hidden(X4,k1_relat_1(sK1))
        | ~ r2_hidden(X4,X5) )
    | ~ spl4_1 ),
    inference(resolution,[],[f43,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f231,plain,
    ( ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f200,f54])).

fof(f200,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f20,f58])).

fof(f58,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f20,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f195,plain,
    ( ~ spl4_1
    | spl4_2
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | ~ spl4_1
    | spl4_2
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f192,f53])).

fof(f53,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f192,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl4_1
    | ~ spl4_10 ),
    inference(trivial_inequality_removal,[],[f190])).

fof(f190,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl4_1
    | ~ spl4_10 ),
    inference(superposition,[],[f65,f150])).

fof(f150,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl4_10
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f65,plain,
    ( ! [X11] :
        ( k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,X11))
        | k1_xboole_0 = k7_relat_1(sK1,X11) )
    | ~ spl4_1 ),
    inference(resolution,[],[f48,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f48,plain,
    ( ! [X6] : v1_relat_1(k7_relat_1(sK1,X6))
    | ~ spl4_1 ),
    inference(resolution,[],[f43,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f151,plain,
    ( spl4_10
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f129,f56,f41,f148])).

fof(f129,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(resolution,[],[f126,f26])).

% (17190)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f126,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f92,f46])).

fof(f46,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,k1_relat_1(sK1))
        | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(sK1,X3))) )
    | ~ spl4_1 ),
    inference(resolution,[],[f43,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f92,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_relat_1(k7_relat_1(sK1,sK0)))
        | ~ r2_hidden(X2,k1_relat_1(sK1)) )
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(resolution,[],[f45,f60])).

fof(f60,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl4_3 ),
    inference(resolution,[],[f58,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f123,plain,
    ( spl4_9
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f109,f41,f120])).

fof(f109,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_xboole_0))
    | ~ spl4_1 ),
    inference(resolution,[],[f106,f26])).

fof(f59,plain,
    ( spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f19,f56,f52])).

fof(f19,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (17200)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (17188)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.46  % (17189)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.46  % (17200)Refutation not found, incomplete strategy% (17200)------------------------------
% 0.20/0.46  % (17200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (17192)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.46  % (17200)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (17200)Memory used [KB]: 10490
% 0.20/0.46  % (17200)Time elapsed: 0.047 s
% 0.20/0.46  % (17200)------------------------------
% 0.20/0.46  % (17200)------------------------------
% 0.20/0.46  % (17181)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.46  % (17182)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (17193)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (17183)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (17182)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f410,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f44,f59,f123,f151,f195,f231,f404,f409])).
% 0.20/0.48  fof(f409,plain,(
% 0.20/0.48    spl4_3 | spl4_14),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f408])).
% 0.20/0.48  fof(f408,plain,(
% 0.20/0.48    $false | (spl4_3 | spl4_14)),
% 0.20/0.48    inference(subsumption_resolution,[],[f405,f57])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl4_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f56])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    spl4_3 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.48  fof(f405,plain,(
% 0.20/0.48    r1_xboole_0(k1_relat_1(sK1),sK0) | spl4_14),
% 0.20/0.48    inference(resolution,[],[f403,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.48  fof(f403,plain,(
% 0.20/0.48    ~r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_relat_1(sK1)) | spl4_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f401])).
% 0.20/0.48  fof(f401,plain,(
% 0.20/0.48    spl4_14 <=> r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_relat_1(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.48  fof(f404,plain,(
% 0.20/0.48    ~spl4_14 | ~spl4_1 | ~spl4_2 | spl4_3 | ~spl4_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f311,f120,f56,f52,f41,f401])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    spl4_1 <=> v1_relat_1(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    spl4_2 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    spl4_9 <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_xboole_0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.48  fof(f311,plain,(
% 0.20/0.48    ~r2_hidden(sK3(k1_relat_1(sK1),sK0),k1_relat_1(sK1)) | (~spl4_1 | ~spl4_2 | spl4_3 | ~spl4_9)),
% 0.20/0.48    inference(resolution,[],[f238,f57])).
% 0.20/0.48  fof(f238,plain,(
% 0.20/0.48    ( ! [X0] : (r1_xboole_0(X0,sK0) | ~r2_hidden(sK3(X0,sK0),k1_relat_1(sK1))) ) | (~spl4_1 | ~spl4_2 | ~spl4_9)),
% 0.20/0.48    inference(resolution,[],[f234,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f234,plain,(
% 0.20/0.48    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r2_hidden(X1,k1_relat_1(sK1))) ) | (~spl4_1 | ~spl4_2 | ~spl4_9)),
% 0.20/0.48    inference(subsumption_resolution,[],[f233,f136])).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) ) | (~spl4_1 | ~spl4_9)),
% 0.20/0.48    inference(superposition,[],[f106,f122])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_xboole_0)) | ~spl4_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f120])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,k1_xboole_0)))) ) | ~spl4_1),
% 0.20/0.48    inference(superposition,[],[f91,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,k2_zfmisc_1(X0,X1))))) ) | ~spl4_1),
% 0.20/0.48    inference(resolution,[],[f45,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1)))) ) | ~spl4_1),
% 0.20/0.48    inference(resolution,[],[f43,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    v1_relat_1(sK1) | ~spl4_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f41])).
% 0.20/0.48  fof(f233,plain,(
% 0.20/0.48    ( ! [X1] : (r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,k1_relat_1(sK1)) | ~r2_hidden(X1,sK0)) ) | (~spl4_1 | ~spl4_2)),
% 0.20/0.48    inference(forward_demodulation,[],[f212,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.48  fof(f212,plain,(
% 0.20/0.48    ( ! [X1] : (r2_hidden(X1,k1_relat_1(k1_xboole_0)) | ~r2_hidden(X1,k1_relat_1(sK1)) | ~r2_hidden(X1,sK0)) ) | (~spl4_1 | ~spl4_2)),
% 0.20/0.48    inference(superposition,[],[f47,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl4_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f52])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X4,X5] : (r2_hidden(X4,k1_relat_1(k7_relat_1(sK1,X5))) | ~r2_hidden(X4,k1_relat_1(sK1)) | ~r2_hidden(X4,X5)) ) | ~spl4_1),
% 0.20/0.48    inference(resolution,[],[f43,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f231,plain,(
% 0.20/0.48    ~spl4_2 | ~spl4_3),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f230])).
% 0.20/0.48  fof(f230,plain,(
% 0.20/0.48    $false | (~spl4_2 | ~spl4_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f200,f54])).
% 0.20/0.48  fof(f200,plain,(
% 0.20/0.48    k1_xboole_0 != k7_relat_1(sK1,sK0) | ~spl4_3),
% 0.20/0.48    inference(subsumption_resolution,[],[f20,f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl4_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f56])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.48    inference(negated_conjecture,[],[f9])).
% 0.20/0.48  fof(f9,conjecture,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.20/0.48  fof(f195,plain,(
% 0.20/0.48    ~spl4_1 | spl4_2 | ~spl4_10),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f194])).
% 0.20/0.48  fof(f194,plain,(
% 0.20/0.48    $false | (~spl4_1 | spl4_2 | ~spl4_10)),
% 0.20/0.48    inference(subsumption_resolution,[],[f192,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    k1_xboole_0 != k7_relat_1(sK1,sK0) | spl4_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f52])).
% 0.20/0.48  fof(f192,plain,(
% 0.20/0.48    k1_xboole_0 = k7_relat_1(sK1,sK0) | (~spl4_1 | ~spl4_10)),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f190])).
% 0.20/0.48  fof(f190,plain,(
% 0.20/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(sK1,sK0) | (~spl4_1 | ~spl4_10)),
% 0.20/0.48    inference(superposition,[],[f65,f150])).
% 0.20/0.48  fof(f150,plain,(
% 0.20/0.48    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~spl4_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f148])).
% 0.20/0.48  fof(f148,plain,(
% 0.20/0.48    spl4_10 <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    ( ! [X11] : (k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,X11)) | k1_xboole_0 = k7_relat_1(sK1,X11)) ) | ~spl4_1),
% 0.20/0.48    inference(resolution,[],[f48,f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X6] : (v1_relat_1(k7_relat_1(sK1,X6))) ) | ~spl4_1),
% 0.20/0.48    inference(resolution,[],[f43,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.48  fof(f151,plain,(
% 0.20/0.48    spl4_10 | ~spl4_1 | ~spl4_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f129,f56,f41,f148])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | (~spl4_1 | ~spl4_3)),
% 0.20/0.48    inference(resolution,[],[f126,f26])).
% 0.20/0.48  % (17190)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(k7_relat_1(sK1,sK0)))) ) | (~spl4_1 | ~spl4_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f92,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X2,X3] : (r2_hidden(X2,k1_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(k7_relat_1(sK1,X3)))) ) | ~spl4_1),
% 0.20/0.48    inference(resolution,[],[f43,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(k7_relat_1(sK1,sK0))) | ~r2_hidden(X2,k1_relat_1(sK1))) ) | (~spl4_1 | ~spl4_3)),
% 0.20/0.48    inference(resolution,[],[f45,f60])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl4_3),
% 0.20/0.48    inference(resolution,[],[f58,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    spl4_9 | ~spl4_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f109,f41,f120])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,k1_xboole_0)) | ~spl4_1),
% 0.20/0.48    inference(resolution,[],[f106,f26])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    spl4_2 | spl4_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f19,f56,f52])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    spl4_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f21,f41])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    v1_relat_1(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (17182)------------------------------
% 0.20/0.48  % (17182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17182)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (17182)Memory used [KB]: 10746
% 0.20/0.48  % (17182)Time elapsed: 0.068 s
% 0.20/0.48  % (17182)------------------------------
% 0.20/0.48  % (17182)------------------------------
% 0.20/0.49  % (17179)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (17178)Success in time 0.13 s
%------------------------------------------------------------------------------
