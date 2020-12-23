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
% DateTime   : Thu Dec  3 12:47:56 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 148 expanded)
%              Number of leaves         :   22 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :  249 ( 365 expanded)
%              Number of equality atoms :   44 (  80 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f326,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f61,f70,f79,f135,f197,f203,f227,f230,f263,f316,f325])).

fof(f325,plain,
    ( spl1_2
    | ~ spl1_32 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | spl1_2
    | ~ spl1_32 ),
    inference(trivial_inequality_removal,[],[f322])).

fof(f322,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_2
    | ~ spl1_32 ),
    inference(superposition,[],[f44,f288])).

fof(f288,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl1_32 ),
    inference(resolution,[],[f226,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f38,f28])).

fof(f28,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f226,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_32 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl1_32
  <=> v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_32])])).

fof(f44,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl1_2
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f316,plain,
    ( spl1_1
    | ~ spl1_26 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | spl1_1
    | ~ spl1_26 ),
    inference(trivial_inequality_removal,[],[f313])).

fof(f313,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_1
    | ~ spl1_26 ),
    inference(superposition,[],[f41,f234])).

fof(f234,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_26 ),
    inference(resolution,[],[f196,f48])).

fof(f196,plain,
    ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_26 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl1_26
  <=> v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_26])])).

fof(f41,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl1_1
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f263,plain,
    ( ~ spl1_3
    | ~ spl1_27
    | spl1_28 ),
    inference(avatar_split_clause,[],[f261,f210,f201,f56])).

fof(f56,plain,
    ( spl1_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f201,plain,
    ( spl1_27
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_27])])).

fof(f210,plain,
    ( spl1_28
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).

fof(f261,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl1_28 ),
    inference(resolution,[],[f211,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f211,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl1_28 ),
    inference(avatar_component_clause,[],[f210])).

fof(f230,plain,(
    spl1_27 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | spl1_27 ),
    inference(resolution,[],[f202,f27])).

fof(f27,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f202,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_27 ),
    inference(avatar_component_clause,[],[f201])).

fof(f227,plain,
    ( spl1_32
    | ~ spl1_28
    | ~ spl1_16
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f208,f77,f123,f210,f225])).

fof(f123,plain,
    ( spl1_16
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f77,plain,
    ( spl1_7
  <=> ! [X0] :
        ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k1_xboole_0,k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

% (25267)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% (25283)Termination reason: Refutation not found, incomplete strategy

% (25283)Memory used [KB]: 10618
% (25283)Time elapsed: 0.057 s
% (25283)------------------------------
% (25283)------------------------------
% (25267)Refutation not found, incomplete strategy% (25267)------------------------------
% (25267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25267)Termination reason: Refutation not found, incomplete strategy

% (25270)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% (25267)Memory used [KB]: 6140
% (25267)Time elapsed: 0.056 s
% (25267)------------------------------
% (25267)------------------------------
% (25282)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% (25264)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% (25270)Refutation not found, incomplete strategy% (25270)------------------------------
% (25270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f208,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_7 ),
    inference(superposition,[],[f35,f167])).

fof(f167,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_7 ),
    inference(resolution,[],[f89,f27])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) )
    | ~ spl1_7 ),
    inference(resolution,[],[f78,f31])).

fof(f31,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f78,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f77])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f203,plain,
    ( ~ spl1_27
    | ~ spl1_3
    | spl1_22 ),
    inference(avatar_split_clause,[],[f198,f180,f56,f201])).

fof(f180,plain,
    ( spl1_22
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).

fof(f198,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl1_22 ),
    inference(resolution,[],[f181,f37])).

fof(f181,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl1_22 ),
    inference(avatar_component_clause,[],[f180])).

fof(f197,plain,
    ( spl1_26
    | ~ spl1_22
    | ~ spl1_16
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f178,f59,f123,f180,f195])).

fof(f59,plain,
    ( spl1_4
  <=> ! [X0] :
        ( k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k1_xboole_0,k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f178,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_4 ),
    inference(superposition,[],[f36,f163])).

fof(f163,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_4 ),
    inference(resolution,[],[f80,f27])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) )
    | ~ spl1_4 ),
    inference(resolution,[],[f60,f31])).

fof(f60,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) )
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f135,plain,(
    spl1_16 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | spl1_16 ),
    inference(resolution,[],[f124,f28])).

fof(f124,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_16 ),
    inference(avatar_component_clause,[],[f123])).

fof(f79,plain,
    ( ~ spl1_3
    | spl1_7 ),
    inference(avatar_split_clause,[],[f75,f77,f56])).

fof(f75,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f67,f29])).

fof(f29,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) ) ),
    inference(superposition,[],[f34,f30])).

fof(f30,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f70,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | spl1_3 ),
    inference(resolution,[],[f66,f28])).

fof(f66,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_3 ),
    inference(resolution,[],[f57,f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f57,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f61,plain,
    ( ~ spl1_3
    | spl1_4 ),
    inference(avatar_split_clause,[],[f54,f59,f56])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f52,f30])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0)
      | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) ) ),
    inference(superposition,[],[f33,f29])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f45,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f26,f43,f40])).

fof(f26,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n017.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 13:56:31 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.17/0.45  % (25265)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.17/0.46  % (25272)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.17/0.47  % (25278)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.17/0.47  % (25268)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.17/0.47  % (25277)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.17/0.47  % (25266)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.17/0.47  % (25281)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.17/0.47  % (25276)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.17/0.47  % (25283)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.17/0.47  % (25275)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.17/0.48  % (25261)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.17/0.48  % (25263)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.17/0.48  % (25260)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.17/0.48  % (25263)Refutation not found, incomplete strategy% (25263)------------------------------
% 0.17/0.48  % (25263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.48  % (25263)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.48  
% 0.17/0.48  % (25263)Memory used [KB]: 10490
% 0.17/0.48  % (25263)Time elapsed: 0.091 s
% 0.17/0.48  % (25263)------------------------------
% 0.17/0.48  % (25263)------------------------------
% 0.17/0.48  % (25262)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.17/0.48  % (25283)Refutation not found, incomplete strategy% (25283)------------------------------
% 0.17/0.48  % (25283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.48  % (25272)Refutation found. Thanks to Tanya!
% 0.17/0.48  % SZS status Theorem for theBenchmark
% 0.17/0.48  % SZS output start Proof for theBenchmark
% 0.17/0.48  fof(f326,plain,(
% 0.17/0.48    $false),
% 0.17/0.48    inference(avatar_sat_refutation,[],[f45,f61,f70,f79,f135,f197,f203,f227,f230,f263,f316,f325])).
% 0.17/0.48  fof(f325,plain,(
% 0.17/0.48    spl1_2 | ~spl1_32),
% 0.17/0.48    inference(avatar_contradiction_clause,[],[f324])).
% 0.17/0.48  fof(f324,plain,(
% 0.17/0.48    $false | (spl1_2 | ~spl1_32)),
% 0.17/0.48    inference(trivial_inequality_removal,[],[f322])).
% 0.17/0.48  fof(f322,plain,(
% 0.17/0.48    k1_xboole_0 != k1_xboole_0 | (spl1_2 | ~spl1_32)),
% 0.17/0.48    inference(superposition,[],[f44,f288])).
% 0.17/0.48  fof(f288,plain,(
% 0.17/0.48    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | ~spl1_32),
% 0.17/0.48    inference(resolution,[],[f226,f48])).
% 0.17/0.48  fof(f48,plain,(
% 0.17/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.17/0.48    inference(resolution,[],[f38,f28])).
% 0.17/0.48  fof(f28,plain,(
% 0.17/0.48    v1_xboole_0(k1_xboole_0)),
% 0.17/0.48    inference(cnf_transformation,[],[f1])).
% 0.17/0.48  fof(f1,axiom,(
% 0.17/0.48    v1_xboole_0(k1_xboole_0)),
% 0.17/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.17/0.48  fof(f38,plain,(
% 0.17/0.48    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~v1_xboole_0(X0) | X0 = X1) )),
% 0.17/0.48    inference(cnf_transformation,[],[f25])).
% 0.17/0.48  fof(f25,plain,(
% 0.17/0.48    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.17/0.48    inference(ennf_transformation,[],[f3])).
% 0.17/0.48  fof(f3,axiom,(
% 0.17/0.48    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.17/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.17/0.48  fof(f226,plain,(
% 0.17/0.48    v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_32),
% 0.17/0.48    inference(avatar_component_clause,[],[f225])).
% 0.17/0.48  fof(f225,plain,(
% 0.17/0.48    spl1_32 <=> v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 0.17/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_32])])).
% 0.17/0.48  fof(f44,plain,(
% 0.17/0.48    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl1_2),
% 0.17/0.48    inference(avatar_component_clause,[],[f43])).
% 0.17/0.48  fof(f43,plain,(
% 0.17/0.48    spl1_2 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.17/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.17/0.48  fof(f316,plain,(
% 0.17/0.48    spl1_1 | ~spl1_26),
% 0.17/0.48    inference(avatar_contradiction_clause,[],[f315])).
% 0.17/0.48  fof(f315,plain,(
% 0.17/0.48    $false | (spl1_1 | ~spl1_26)),
% 0.17/0.48    inference(trivial_inequality_removal,[],[f313])).
% 0.17/0.48  fof(f313,plain,(
% 0.17/0.48    k1_xboole_0 != k1_xboole_0 | (spl1_1 | ~spl1_26)),
% 0.17/0.48    inference(superposition,[],[f41,f234])).
% 0.17/0.48  fof(f234,plain,(
% 0.17/0.48    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~spl1_26),
% 0.17/0.48    inference(resolution,[],[f196,f48])).
% 0.17/0.48  fof(f196,plain,(
% 0.17/0.48    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_26),
% 0.17/0.48    inference(avatar_component_clause,[],[f195])).
% 0.17/0.48  fof(f195,plain,(
% 0.17/0.48    spl1_26 <=> v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 0.17/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_26])])).
% 0.17/0.48  fof(f41,plain,(
% 0.17/0.48    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl1_1),
% 0.17/0.48    inference(avatar_component_clause,[],[f40])).
% 0.17/0.48  fof(f40,plain,(
% 0.17/0.48    spl1_1 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.17/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.17/0.48  fof(f263,plain,(
% 0.17/0.48    ~spl1_3 | ~spl1_27 | spl1_28),
% 0.17/0.48    inference(avatar_split_clause,[],[f261,f210,f201,f56])).
% 0.17/0.48  fof(f56,plain,(
% 0.17/0.48    spl1_3 <=> v1_relat_1(k1_xboole_0)),
% 0.17/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.17/0.48  fof(f201,plain,(
% 0.17/0.48    spl1_27 <=> v1_relat_1(sK0)),
% 0.17/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_27])])).
% 0.17/0.48  fof(f210,plain,(
% 0.17/0.48    spl1_28 <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.17/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).
% 0.17/0.48  fof(f261,plain,(
% 0.17/0.48    ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl1_28),
% 0.17/0.48    inference(resolution,[],[f211,f37])).
% 0.17/0.48  fof(f37,plain,(
% 0.17/0.48    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.17/0.48    inference(cnf_transformation,[],[f24])).
% 0.17/0.48  fof(f24,plain,(
% 0.17/0.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.17/0.48    inference(flattening,[],[f23])).
% 0.17/0.48  fof(f23,plain,(
% 0.17/0.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.17/0.48    inference(ennf_transformation,[],[f5])).
% 0.17/0.48  fof(f5,axiom,(
% 0.17/0.48    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.17/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.17/0.48  fof(f211,plain,(
% 0.17/0.48    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl1_28),
% 0.17/0.48    inference(avatar_component_clause,[],[f210])).
% 0.17/0.48  fof(f230,plain,(
% 0.17/0.48    spl1_27),
% 0.17/0.48    inference(avatar_contradiction_clause,[],[f228])).
% 0.17/0.48  fof(f228,plain,(
% 0.17/0.48    $false | spl1_27),
% 0.17/0.48    inference(resolution,[],[f202,f27])).
% 0.17/0.48  fof(f27,plain,(
% 0.17/0.48    v1_relat_1(sK0)),
% 0.17/0.48    inference(cnf_transformation,[],[f13])).
% 0.17/0.48  fof(f13,plain,(
% 0.17/0.48    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.17/0.48    inference(ennf_transformation,[],[f12])).
% 0.17/0.48  fof(f12,negated_conjecture,(
% 0.17/0.48    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.17/0.48    inference(negated_conjecture,[],[f11])).
% 0.17/0.48  fof(f11,conjecture,(
% 0.17/0.48    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.17/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.17/0.48  fof(f202,plain,(
% 0.17/0.48    ~v1_relat_1(sK0) | spl1_27),
% 0.17/0.48    inference(avatar_component_clause,[],[f201])).
% 0.17/0.48  fof(f227,plain,(
% 0.17/0.48    spl1_32 | ~spl1_28 | ~spl1_16 | ~spl1_7),
% 0.17/0.48    inference(avatar_split_clause,[],[f208,f77,f123,f210,f225])).
% 0.17/0.48  fof(f123,plain,(
% 0.17/0.48    spl1_16 <=> v1_xboole_0(k1_xboole_0)),
% 0.17/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.17/0.48  fof(f77,plain,(
% 0.17/0.48    spl1_7 <=> ! [X0] : (k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~r1_tarski(k1_xboole_0,k1_relat_1(X0)))),
% 0.17/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.17/0.48  % (25267)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.17/0.48  % (25283)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.48  
% 0.17/0.48  % (25283)Memory used [KB]: 10618
% 0.17/0.48  % (25283)Time elapsed: 0.057 s
% 0.17/0.48  % (25283)------------------------------
% 0.17/0.48  % (25283)------------------------------
% 0.17/0.48  % (25267)Refutation not found, incomplete strategy% (25267)------------------------------
% 0.17/0.48  % (25267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.48  % (25267)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.48  
% 0.17/0.48  % (25270)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.17/0.48  % (25267)Memory used [KB]: 6140
% 0.17/0.48  % (25267)Time elapsed: 0.056 s
% 0.17/0.48  % (25267)------------------------------
% 0.17/0.48  % (25267)------------------------------
% 0.17/0.48  % (25282)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.17/0.48  % (25264)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.17/0.49  % (25270)Refutation not found, incomplete strategy% (25270)------------------------------
% 0.17/0.49  % (25270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.49  fof(f208,plain,(
% 0.17/0.49    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_7),
% 0.17/0.49    inference(superposition,[],[f35,f167])).
% 0.17/0.49  fof(f167,plain,(
% 0.17/0.49    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_7),
% 0.17/0.49    inference(resolution,[],[f89,f27])).
% 0.17/0.49  fof(f89,plain,(
% 0.17/0.49    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) ) | ~spl1_7),
% 0.17/0.49    inference(resolution,[],[f78,f31])).
% 0.17/0.49  fof(f31,plain,(
% 0.17/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.17/0.49    inference(cnf_transformation,[],[f2])).
% 0.17/0.49  fof(f2,axiom,(
% 0.17/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.17/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.17/0.49  fof(f78,plain,(
% 0.17/0.49    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) ) | ~spl1_7),
% 0.17/0.49    inference(avatar_component_clause,[],[f77])).
% 0.17/0.49  fof(f35,plain,(
% 0.17/0.49    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.17/0.49    inference(cnf_transformation,[],[f20])).
% 0.17/0.49  fof(f20,plain,(
% 0.17/0.49    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.17/0.49    inference(flattening,[],[f19])).
% 0.17/0.49  fof(f19,plain,(
% 0.17/0.49    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.17/0.49    inference(ennf_transformation,[],[f6])).
% 0.17/0.49  fof(f6,axiom,(
% 0.17/0.49    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.17/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.17/0.49  fof(f203,plain,(
% 0.17/0.49    ~spl1_27 | ~spl1_3 | spl1_22),
% 0.17/0.49    inference(avatar_split_clause,[],[f198,f180,f56,f201])).
% 0.17/0.49  fof(f180,plain,(
% 0.17/0.49    spl1_22 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.17/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).
% 0.17/0.49  fof(f198,plain,(
% 0.17/0.49    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | spl1_22),
% 0.17/0.49    inference(resolution,[],[f181,f37])).
% 0.17/0.49  fof(f181,plain,(
% 0.17/0.49    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl1_22),
% 0.17/0.49    inference(avatar_component_clause,[],[f180])).
% 0.17/0.49  fof(f197,plain,(
% 0.17/0.49    spl1_26 | ~spl1_22 | ~spl1_16 | ~spl1_4),
% 0.17/0.49    inference(avatar_split_clause,[],[f178,f59,f123,f180,f195])).
% 0.17/0.49  fof(f59,plain,(
% 0.17/0.49    spl1_4 <=> ! [X0] : (k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~r1_tarski(k1_xboole_0,k2_relat_1(X0)))),
% 0.17/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.17/0.49  fof(f178,plain,(
% 0.17/0.49    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_4),
% 0.17/0.49    inference(superposition,[],[f36,f163])).
% 0.17/0.49  fof(f163,plain,(
% 0.17/0.49    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_4),
% 0.17/0.49    inference(resolution,[],[f80,f27])).
% 0.17/0.49  fof(f80,plain,(
% 0.17/0.49    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) ) | ~spl1_4),
% 0.17/0.49    inference(resolution,[],[f60,f31])).
% 0.17/0.49  fof(f60,plain,(
% 0.17/0.49    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) ) | ~spl1_4),
% 0.17/0.49    inference(avatar_component_clause,[],[f59])).
% 0.17/0.49  fof(f36,plain,(
% 0.17/0.49    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.17/0.49    inference(cnf_transformation,[],[f22])).
% 0.17/0.49  fof(f22,plain,(
% 0.17/0.49    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.17/0.49    inference(flattening,[],[f21])).
% 0.17/0.49  fof(f21,plain,(
% 0.17/0.49    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.17/0.49    inference(ennf_transformation,[],[f7])).
% 0.17/0.49  fof(f7,axiom,(
% 0.17/0.49    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.17/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.17/0.49  fof(f135,plain,(
% 0.17/0.49    spl1_16),
% 0.17/0.49    inference(avatar_contradiction_clause,[],[f134])).
% 0.17/0.49  fof(f134,plain,(
% 0.17/0.49    $false | spl1_16),
% 0.17/0.49    inference(resolution,[],[f124,f28])).
% 0.17/0.49  fof(f124,plain,(
% 0.17/0.49    ~v1_xboole_0(k1_xboole_0) | spl1_16),
% 0.17/0.49    inference(avatar_component_clause,[],[f123])).
% 0.17/0.49  fof(f79,plain,(
% 0.17/0.49    ~spl1_3 | spl1_7),
% 0.17/0.49    inference(avatar_split_clause,[],[f75,f77,f56])).
% 0.17/0.49  fof(f75,plain,(
% 0.17/0.49    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.17/0.49    inference(forward_demodulation,[],[f67,f29])).
% 0.17/0.49  fof(f29,plain,(
% 0.17/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.17/0.49    inference(cnf_transformation,[],[f10])).
% 0.17/0.49  fof(f10,axiom,(
% 0.17/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.17/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.17/0.49  fof(f67,plain,(
% 0.17/0.49    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) )),
% 0.17/0.49    inference(superposition,[],[f34,f30])).
% 0.17/0.49  fof(f30,plain,(
% 0.17/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.17/0.49    inference(cnf_transformation,[],[f10])).
% 0.17/0.49  fof(f34,plain,(
% 0.17/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))) )),
% 0.17/0.49    inference(cnf_transformation,[],[f18])).
% 0.17/0.49  fof(f18,plain,(
% 0.17/0.49    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.17/0.49    inference(flattening,[],[f17])).
% 0.17/0.49  fof(f17,plain,(
% 0.17/0.49    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.17/0.49    inference(ennf_transformation,[],[f8])).
% 0.17/0.49  fof(f8,axiom,(
% 0.17/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.17/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.17/0.49  fof(f70,plain,(
% 0.17/0.49    spl1_3),
% 0.17/0.49    inference(avatar_contradiction_clause,[],[f69])).
% 0.17/0.49  fof(f69,plain,(
% 0.17/0.49    $false | spl1_3),
% 0.17/0.49    inference(resolution,[],[f66,f28])).
% 0.17/0.49  fof(f66,plain,(
% 0.17/0.49    ~v1_xboole_0(k1_xboole_0) | spl1_3),
% 0.17/0.49    inference(resolution,[],[f57,f32])).
% 0.17/0.49  fof(f32,plain,(
% 0.17/0.49    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.17/0.49    inference(cnf_transformation,[],[f14])).
% 0.17/0.49  fof(f14,plain,(
% 0.17/0.49    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.17/0.49    inference(ennf_transformation,[],[f4])).
% 0.17/0.49  fof(f4,axiom,(
% 0.17/0.49    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.17/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.17/0.49  fof(f57,plain,(
% 0.17/0.49    ~v1_relat_1(k1_xboole_0) | spl1_3),
% 0.17/0.49    inference(avatar_component_clause,[],[f56])).
% 0.17/0.49  fof(f61,plain,(
% 0.17/0.49    ~spl1_3 | spl1_4),
% 0.17/0.49    inference(avatar_split_clause,[],[f54,f59,f56])).
% 0.17/0.49  fof(f54,plain,(
% 0.17/0.49    ( ! [X0] : (k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.17/0.49    inference(forward_demodulation,[],[f52,f30])).
% 0.17/0.49  fof(f52,plain,(
% 0.17/0.49    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0) | k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) )),
% 0.17/0.49    inference(superposition,[],[f33,f29])).
% 0.17/0.49  fof(f33,plain,(
% 0.17/0.49    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))) )),
% 0.17/0.49    inference(cnf_transformation,[],[f16])).
% 0.17/0.49  fof(f16,plain,(
% 0.17/0.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.17/0.49    inference(flattening,[],[f15])).
% 0.17/0.49  fof(f15,plain,(
% 0.17/0.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.17/0.49    inference(ennf_transformation,[],[f9])).
% 0.17/0.49  fof(f9,axiom,(
% 0.17/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.17/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 0.17/0.49  fof(f45,plain,(
% 0.17/0.49    ~spl1_1 | ~spl1_2),
% 0.17/0.49    inference(avatar_split_clause,[],[f26,f43,f40])).
% 0.17/0.49  fof(f26,plain,(
% 0.17/0.49    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 0.17/0.49    inference(cnf_transformation,[],[f13])).
% 0.17/0.49  % SZS output end Proof for theBenchmark
% 0.17/0.49  % (25272)------------------------------
% 0.17/0.49  % (25272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.49  % (25272)Termination reason: Refutation
% 0.17/0.49  
% 0.17/0.49  % (25272)Memory used [KB]: 10746
% 0.17/0.49  % (25273)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.17/0.49  % (25272)Time elapsed: 0.111 s
% 0.17/0.49  % (25272)------------------------------
% 0.17/0.49  % (25272)------------------------------
% 0.17/0.49  % (25270)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.49  
% 0.17/0.49  % (25270)Memory used [KB]: 10490
% 0.17/0.49  % (25270)Time elapsed: 0.108 s
% 0.17/0.49  % (25270)------------------------------
% 0.17/0.49  % (25270)------------------------------
% 0.17/0.49  % (25259)Success in time 0.158 s
%------------------------------------------------------------------------------
