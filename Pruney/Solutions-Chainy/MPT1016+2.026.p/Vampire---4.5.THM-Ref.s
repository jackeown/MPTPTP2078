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
% DateTime   : Thu Dec  3 13:05:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 320 expanded)
%              Number of leaves         :   26 ( 107 expanded)
%              Depth                    :   15
%              Number of atoms          :  553 (2072 expanded)
%              Number of equality atoms :  140 ( 606 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f242,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f92,f97,f101,f126,f149,f153,f175,f179,f193,f194,f225,f241])).

fof(f241,plain,
    ( ~ spl11_1
    | spl11_7 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | ~ spl11_1
    | spl11_7 ),
    inference(subsumption_resolution,[],[f239,f42])).

fof(f42,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ( sK7 != sK8
        & k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8)
        & r2_hidden(sK8,sK5)
        & r2_hidden(sK7,sK5) )
      | ~ v2_funct_1(sK6) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK6,X4) != k1_funct_1(sK6,X5)
          | ~ r2_hidden(X5,sK5)
          | ~ r2_hidden(X4,sK5) )
      | v2_funct_1(sK6) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))
    & v1_funct_2(sK6,sK5,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f28,f30,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | v2_funct_1(X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ? [X3,X2] :
            ( X2 != X3
            & k1_funct_1(sK6,X2) = k1_funct_1(sK6,X3)
            & r2_hidden(X3,sK5)
            & r2_hidden(X2,sK5) )
        | ~ v2_funct_1(sK6) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK6,X4) != k1_funct_1(sK6,X5)
            | ~ r2_hidden(X5,sK5)
            | ~ r2_hidden(X4,sK5) )
        | v2_funct_1(sK6) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))
      & v1_funct_2(sK6,sK5,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

% (11937)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f30,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK6,X2) = k1_funct_1(sK6,X3)
        & r2_hidden(X3,sK5)
        & r2_hidden(X2,sK5) )
   => ( sK7 != sK8
      & k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8)
      & r2_hidden(sK8,sK5)
      & r2_hidden(sK7,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
            | ~ r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

fof(f239,plain,
    ( ~ v1_funct_1(sK6)
    | ~ spl11_1
    | spl11_7 ),
    inference(subsumption_resolution,[],[f238,f76])).

% (11929)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (11941)Refutation not found, incomplete strategy% (11941)------------------------------
% (11941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11947)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (11941)Termination reason: Refutation not found, incomplete strategy

% (11941)Memory used [KB]: 6140
% (11941)Time elapsed: 0.132 s
% (11941)------------------------------
% (11941)------------------------------
% (11938)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f76,plain,
    ( v2_funct_1(sK6)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl11_1
  <=> v2_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f238,plain,
    ( ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | spl11_7 ),
    inference(subsumption_resolution,[],[f237,f107])).

fof(f107,plain,(
    v1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f106,f59])).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f106,plain,
    ( v1_relat_1(sK6)
    | ~ v1_relat_1(k2_zfmisc_1(sK5,sK5)) ),
    inference(resolution,[],[f50,f44])).

fof(f44,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f237,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | spl11_7 ),
    inference(resolution,[],[f116,f103])).

fof(f103,plain,(
    ! [X1] :
      ( sP0(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f58,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v2_funct_1(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f58,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f13,f20,f19])).

fof(f19,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1,X2] :
          ( X1 = X2
          | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
          | ~ r2_hidden(X2,k1_relat_1(X0))
          | ~ r2_hidden(X1,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f116,plain,
    ( ~ sP0(sK6)
    | spl11_7 ),
    inference(avatar_component_clause,[],[f115])).

% (11944)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f115,plain,
    ( spl11_7
  <=> sP0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f225,plain,
    ( spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_10 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f223,f81])).

fof(f81,plain,
    ( sK7 != sK8
    | spl11_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl11_2
  <=> sK7 = sK8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f223,plain,
    ( sK7 = sK8
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f222,f96])).

fof(f96,plain,
    ( r2_hidden(sK7,sK5)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl11_5
  <=> r2_hidden(sK7,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f222,plain,
    ( ~ r2_hidden(sK7,sK5)
    | sK7 = sK8
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_10 ),
    inference(equality_resolution,[],[f201])).

fof(f201,plain,
    ( ! [X0] :
        ( k1_funct_1(sK6,sK7) != k1_funct_1(sK6,X0)
        | ~ r2_hidden(X0,sK5)
        | sK8 = X0 )
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_10 ),
    inference(forward_demodulation,[],[f200,f144])).

fof(f144,plain,
    ( sK5 = k1_relat_1(sK6)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl11_10
  <=> sK5 = k1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f200,plain,
    ( ! [X0] :
        ( k1_funct_1(sK6,sK7) != k1_funct_1(sK6,X0)
        | sK8 = X0
        | ~ r2_hidden(X0,k1_relat_1(sK6)) )
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f199,f91])).

% (11928)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f91,plain,
    ( r2_hidden(sK8,sK5)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl11_4
  <=> r2_hidden(sK8,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f199,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK8,sK5)
        | k1_funct_1(sK6,sK7) != k1_funct_1(sK6,X0)
        | sK8 = X0
        | ~ r2_hidden(X0,k1_relat_1(sK6)) )
    | ~ spl11_3
    | ~ spl11_7
    | ~ spl11_10 ),
    inference(forward_demodulation,[],[f198,f144])).

fof(f198,plain,
    ( ! [X0] :
        ( k1_funct_1(sK6,sK7) != k1_funct_1(sK6,X0)
        | sK8 = X0
        | ~ r2_hidden(sK8,k1_relat_1(sK6))
        | ~ r2_hidden(X0,k1_relat_1(sK6)) )
    | ~ spl11_3
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f196,f117])).

fof(f117,plain,
    ( sP0(sK6)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f196,plain,
    ( ! [X0] :
        ( k1_funct_1(sK6,sK7) != k1_funct_1(sK6,X0)
        | sK8 = X0
        | ~ r2_hidden(sK8,k1_relat_1(sK6))
        | ~ r2_hidden(X0,k1_relat_1(sK6))
        | ~ sP0(sK6) )
    | ~ spl11_3 ),
    inference(superposition,[],[f53,f86])).

fof(f86,plain,
    ( k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl11_3
  <=> k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f53,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( sK9(X0) != sK10(X0)
          & k1_funct_1(X0,sK9(X0)) = k1_funct_1(X0,sK10(X0))
          & r2_hidden(sK10(X0),k1_relat_1(X0))
          & r2_hidden(sK9(X0),k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK9(X0) != sK10(X0)
        & k1_funct_1(X0,sK9(X0)) = k1_funct_1(X0,sK10(X0))
        & r2_hidden(sK10(X0),k1_relat_1(X0))
        & r2_hidden(sK9(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            & r2_hidden(X2,k1_relat_1(X0))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            & r2_hidden(X2,k1_relat_1(X0))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f194,plain,
    ( spl11_1
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f161,f115,f75])).

fof(f161,plain,
    ( v2_funct_1(sK6)
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f160,f42])).

fof(f160,plain,
    ( ~ v1_funct_1(sK6)
    | v2_funct_1(sK6)
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f159,f107])).

fof(f159,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK6)
    | v2_funct_1(sK6)
    | ~ spl11_7 ),
    inference(resolution,[],[f117,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v2_funct_1(X0) ) ),
    inference(resolution,[],[f58,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f193,plain,
    ( spl11_7
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | spl11_7
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f191,f116])).

fof(f191,plain,
    ( sP0(sK6)
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(trivial_inequality_removal,[],[f189])).

fof(f189,plain,
    ( sK9(sK6) != sK9(sK6)
    | sP0(sK6)
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(superposition,[],[f57,f186])).

fof(f186,plain,
    ( sK10(sK6) = sK9(sK6)
    | ~ spl11_9
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f185,f157])).

fof(f157,plain,
    ( r2_hidden(sK9(sK6),sK5)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl11_12
  <=> r2_hidden(sK9(sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f185,plain,
    ( sK10(sK6) = sK9(sK6)
    | ~ r2_hidden(sK9(sK6),sK5)
    | ~ spl11_9 ),
    inference(equality_resolution,[],[f124])).

fof(f124,plain,
    ( ! [X0] :
        ( k1_funct_1(sK6,X0) != k1_funct_1(sK6,sK9(sK6))
        | sK10(sK6) = X0
        | ~ r2_hidden(X0,sK5) )
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl11_9
  <=> ! [X0] :
        ( k1_funct_1(sK6,X0) != k1_funct_1(sK6,sK9(sK6))
        | sK10(sK6) = X0
        | ~ r2_hidden(X0,sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f57,plain,(
    ! [X0] :
      ( sK9(X0) != sK10(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f179,plain,
    ( spl11_12
    | spl11_7
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f178,f142,f115,f155])).

fof(f178,plain,
    ( r2_hidden(sK9(sK6),sK5)
    | spl11_7
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f177,f116])).

fof(f177,plain,
    ( r2_hidden(sK9(sK6),sK5)
    | sP0(sK6)
    | ~ spl11_10 ),
    inference(superposition,[],[f54,f144])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK9(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f175,plain,(
    ~ spl11_11 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f172,f73])).

fof(f73,plain,(
    ! [X1] : ~ sP2(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f172,plain,
    ( sP2(k1_xboole_0,k1_xboole_0)
    | ~ spl11_11 ),
    inference(backward_demodulation,[],[f148,f165])).

fof(f165,plain,
    ( k1_xboole_0 = sK5
    | ~ spl11_11 ),
    inference(resolution,[],[f148,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f148,plain,
    ( sP2(sK5,sK5)
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl11_11
  <=> sP2(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f153,plain,
    ( spl11_7
    | spl11_8
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f152,f142,f119,f115])).

fof(f119,plain,
    ( spl11_8
  <=> r2_hidden(sK10(sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f152,plain,
    ( sP0(sK6)
    | spl11_8
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f150,f121])).

fof(f121,plain,
    ( ~ r2_hidden(sK10(sK6),sK5)
    | spl11_8 ),
    inference(avatar_component_clause,[],[f119])).

fof(f150,plain,
    ( r2_hidden(sK10(sK6),sK5)
    | sP0(sK6)
    | ~ spl11_10 ),
    inference(superposition,[],[f55,f144])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK10(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f149,plain,
    ( spl11_10
    | spl11_11 ),
    inference(avatar_split_clause,[],[f140,f146,f142])).

fof(f140,plain,
    ( sP2(sK5,sK5)
    | sK5 = k1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f139,f43])).

fof(f43,plain,(
    v1_funct_2(sK6,sK5,sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f139,plain,
    ( ~ v1_funct_2(sK6,sK5,sK5)
    | sP2(sK5,sK5)
    | sK5 = k1_relat_1(sK6) ),
    inference(resolution,[],[f129,f44])).

fof(f129,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP2(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f127,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP3(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X2,X1,X0)
        & sP3(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f16,f24,f23,f22])).

fof(f23,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP2(X0,X1)
      | ~ sP3(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP4(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f127,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP2(X3,X4)
      | ~ sP3(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f63,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP2(X0,X2)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP2(X0,X2)
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP2(X0,X1)
      | ~ sP3(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f126,plain,
    ( spl11_7
    | ~ spl11_8
    | spl11_9
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f113,f99,f123,f119,f115])).

fof(f99,plain,
    ( spl11_6
  <=> ! [X5,X4] :
        ( X4 = X5
        | ~ r2_hidden(X4,sK5)
        | ~ r2_hidden(X5,sK5)
        | k1_funct_1(sK6,X4) != k1_funct_1(sK6,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f113,plain,
    ( ! [X1] :
        ( k1_funct_1(sK6,X1) != k1_funct_1(sK6,sK9(sK6))
        | ~ r2_hidden(sK10(sK6),sK5)
        | ~ r2_hidden(X1,sK5)
        | sK10(sK6) = X1
        | sP0(sK6) )
    | ~ spl11_6 ),
    inference(superposition,[],[f100,f56])).

fof(f56,plain,(
    ! [X0] :
      ( k1_funct_1(X0,sK9(X0)) = k1_funct_1(X0,sK10(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f100,plain,
    ( ! [X4,X5] :
        ( k1_funct_1(sK6,X4) != k1_funct_1(sK6,X5)
        | ~ r2_hidden(X4,sK5)
        | ~ r2_hidden(X5,sK5)
        | X4 = X5 )
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f101,plain,
    ( spl11_1
    | spl11_6 ),
    inference(avatar_split_clause,[],[f45,f99,f75])).

fof(f45,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK6,X4) != k1_funct_1(sK6,X5)
      | ~ r2_hidden(X5,sK5)
      | ~ r2_hidden(X4,sK5)
      | v2_funct_1(sK6) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f97,plain,
    ( ~ spl11_1
    | spl11_5 ),
    inference(avatar_split_clause,[],[f46,f94,f75])).

% (11953)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f46,plain,
    ( r2_hidden(sK7,sK5)
    | ~ v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f92,plain,
    ( ~ spl11_1
    | spl11_4 ),
    inference(avatar_split_clause,[],[f47,f89,f75])).

fof(f47,plain,
    ( r2_hidden(sK8,sK5)
    | ~ v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f87,plain,
    ( ~ spl11_1
    | spl11_3 ),
    inference(avatar_split_clause,[],[f48,f84,f75])).

fof(f48,plain,
    ( k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8)
    | ~ v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f82,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f49,f79,f75])).

fof(f49,plain,
    ( sK7 != sK8
    | ~ v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:35:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.54  % (11936)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.55  % (11949)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.55  % (11950)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.56  % (11952)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.56  % (11942)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.56  % (11933)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.56  % (11940)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.56  % (11932)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.56  % (11946)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.56  % (11934)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.56  % (11941)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (11930)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.56  % (11932)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % (11948)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.56  % (11931)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f242,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f82,f87,f92,f97,f101,f126,f149,f153,f175,f179,f193,f194,f225,f241])).
% 0.22/0.56  fof(f241,plain,(
% 0.22/0.56    ~spl11_1 | spl11_7),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f240])).
% 0.22/0.56  fof(f240,plain,(
% 0.22/0.56    $false | (~spl11_1 | spl11_7)),
% 0.22/0.56    inference(subsumption_resolution,[],[f239,f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    v1_funct_1(sK6)),
% 0.22/0.56    inference(cnf_transformation,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ((sK7 != sK8 & k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8) & r2_hidden(sK8,sK5) & r2_hidden(sK7,sK5)) | ~v2_funct_1(sK6)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK6,X4) != k1_funct_1(sK6,X5) | ~r2_hidden(X5,sK5) | ~r2_hidden(X4,sK5)) | v2_funct_1(sK6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) & v1_funct_2(sK6,sK5,sK5) & v1_funct_1(sK6)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f28,f30,f29])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK6,X2) = k1_funct_1(sK6,X3) & r2_hidden(X3,sK5) & r2_hidden(X2,sK5)) | ~v2_funct_1(sK6)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK6,X4) != k1_funct_1(sK6,X5) | ~r2_hidden(X5,sK5) | ~r2_hidden(X4,sK5)) | v2_funct_1(sK6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5))) & v1_funct_2(sK6,sK5,sK5) & v1_funct_1(sK6))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  % (11937)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK6,X2) = k1_funct_1(sK6,X3) & r2_hidden(X3,sK5) & r2_hidden(X2,sK5)) => (sK7 != sK8 & k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8) & r2_hidden(sK8,sK5) & r2_hidden(sK7,sK5))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.57    inference(rectify,[],[f27])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.57    inference(flattening,[],[f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.57    inference(nnf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,plain,(
% 0.22/0.57    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.57    inference(flattening,[],[f9])).
% 0.22/0.57  fof(f9,plain,(
% 0.22/0.57    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.22/0.57    inference(negated_conjecture,[],[f7])).
% 0.22/0.57  fof(f7,conjecture,(
% 0.22/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).
% 0.22/0.57  fof(f239,plain,(
% 0.22/0.57    ~v1_funct_1(sK6) | (~spl11_1 | spl11_7)),
% 0.22/0.57    inference(subsumption_resolution,[],[f238,f76])).
% 0.22/0.57  % (11929)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.57  % (11941)Refutation not found, incomplete strategy% (11941)------------------------------
% 0.22/0.57  % (11941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (11947)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.57  % (11941)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (11941)Memory used [KB]: 6140
% 0.22/0.57  % (11941)Time elapsed: 0.132 s
% 0.22/0.57  % (11941)------------------------------
% 0.22/0.57  % (11941)------------------------------
% 0.22/0.57  % (11938)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.57  fof(f76,plain,(
% 0.22/0.57    v2_funct_1(sK6) | ~spl11_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f75])).
% 0.22/0.57  fof(f75,plain,(
% 0.22/0.57    spl11_1 <=> v2_funct_1(sK6)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.22/0.57  fof(f238,plain,(
% 0.22/0.57    ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | spl11_7),
% 0.22/0.57    inference(subsumption_resolution,[],[f237,f107])).
% 0.22/0.57  fof(f107,plain,(
% 0.22/0.57    v1_relat_1(sK6)),
% 0.22/0.57    inference(subsumption_resolution,[],[f106,f59])).
% 0.22/0.57  fof(f59,plain,(
% 0.22/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.57  fof(f106,plain,(
% 0.22/0.57    v1_relat_1(sK6) | ~v1_relat_1(k2_zfmisc_1(sK5,sK5))),
% 0.22/0.57    inference(resolution,[],[f50,f44])).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK5,sK5)))),
% 0.22/0.57    inference(cnf_transformation,[],[f31])).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f11])).
% 0.22/0.57  fof(f11,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.57  fof(f237,plain,(
% 0.22/0.57    ~v1_relat_1(sK6) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | spl11_7),
% 0.22/0.57    inference(resolution,[],[f116,f103])).
% 0.22/0.57  fof(f103,plain,(
% 0.22/0.57    ( ! [X1] : (sP0(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X1) | ~v1_funct_1(X1)) )),
% 0.22/0.57    inference(resolution,[],[f58,f51])).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    ( ! [X0] : (~sP1(X0) | ~v2_funct_1(X0) | sP0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f32])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ! [X0] : (((v2_funct_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_funct_1(X0))) | ~sP1(X0))),
% 0.22/0.57    inference(nnf_transformation,[],[f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ! [X0] : ((v2_funct_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.22/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.57  fof(f58,plain,(
% 0.22/0.57    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(definition_folding,[],[f13,f20,f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ! [X0] : (sP0(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))),
% 0.22/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.57  fof(f13,plain,(
% 0.22/0.57    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(flattening,[],[f12])).
% 0.22/0.57  fof(f12,plain,(
% 0.22/0.57    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 0.22/0.57  fof(f116,plain,(
% 0.22/0.57    ~sP0(sK6) | spl11_7),
% 0.22/0.57    inference(avatar_component_clause,[],[f115])).
% 0.22/0.57  % (11944)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.58  fof(f115,plain,(
% 0.22/0.58    spl11_7 <=> sP0(sK6)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 0.22/0.58  fof(f225,plain,(
% 0.22/0.58    spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_5 | ~spl11_7 | ~spl11_10),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f224])).
% 0.22/0.58  fof(f224,plain,(
% 0.22/0.58    $false | (spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_5 | ~spl11_7 | ~spl11_10)),
% 0.22/0.58    inference(subsumption_resolution,[],[f223,f81])).
% 0.22/0.58  fof(f81,plain,(
% 0.22/0.58    sK7 != sK8 | spl11_2),
% 0.22/0.58    inference(avatar_component_clause,[],[f79])).
% 0.22/0.58  fof(f79,plain,(
% 0.22/0.58    spl11_2 <=> sK7 = sK8),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.22/0.58  fof(f223,plain,(
% 0.22/0.58    sK7 = sK8 | (~spl11_3 | ~spl11_4 | ~spl11_5 | ~spl11_7 | ~spl11_10)),
% 0.22/0.58    inference(subsumption_resolution,[],[f222,f96])).
% 0.22/0.58  fof(f96,plain,(
% 0.22/0.58    r2_hidden(sK7,sK5) | ~spl11_5),
% 0.22/0.58    inference(avatar_component_clause,[],[f94])).
% 0.22/0.58  fof(f94,plain,(
% 0.22/0.58    spl11_5 <=> r2_hidden(sK7,sK5)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 0.22/0.58  fof(f222,plain,(
% 0.22/0.58    ~r2_hidden(sK7,sK5) | sK7 = sK8 | (~spl11_3 | ~spl11_4 | ~spl11_7 | ~spl11_10)),
% 0.22/0.58    inference(equality_resolution,[],[f201])).
% 0.22/0.58  fof(f201,plain,(
% 0.22/0.58    ( ! [X0] : (k1_funct_1(sK6,sK7) != k1_funct_1(sK6,X0) | ~r2_hidden(X0,sK5) | sK8 = X0) ) | (~spl11_3 | ~spl11_4 | ~spl11_7 | ~spl11_10)),
% 0.22/0.58    inference(forward_demodulation,[],[f200,f144])).
% 0.22/0.58  fof(f144,plain,(
% 0.22/0.58    sK5 = k1_relat_1(sK6) | ~spl11_10),
% 0.22/0.58    inference(avatar_component_clause,[],[f142])).
% 0.22/0.58  fof(f142,plain,(
% 0.22/0.58    spl11_10 <=> sK5 = k1_relat_1(sK6)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 0.22/0.58  fof(f200,plain,(
% 0.22/0.58    ( ! [X0] : (k1_funct_1(sK6,sK7) != k1_funct_1(sK6,X0) | sK8 = X0 | ~r2_hidden(X0,k1_relat_1(sK6))) ) | (~spl11_3 | ~spl11_4 | ~spl11_7 | ~spl11_10)),
% 0.22/0.58    inference(subsumption_resolution,[],[f199,f91])).
% 0.22/0.58  % (11928)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.58  fof(f91,plain,(
% 0.22/0.58    r2_hidden(sK8,sK5) | ~spl11_4),
% 0.22/0.58    inference(avatar_component_clause,[],[f89])).
% 0.22/0.58  fof(f89,plain,(
% 0.22/0.58    spl11_4 <=> r2_hidden(sK8,sK5)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.22/0.58  fof(f199,plain,(
% 0.22/0.58    ( ! [X0] : (~r2_hidden(sK8,sK5) | k1_funct_1(sK6,sK7) != k1_funct_1(sK6,X0) | sK8 = X0 | ~r2_hidden(X0,k1_relat_1(sK6))) ) | (~spl11_3 | ~spl11_7 | ~spl11_10)),
% 0.22/0.58    inference(forward_demodulation,[],[f198,f144])).
% 0.22/0.58  fof(f198,plain,(
% 0.22/0.58    ( ! [X0] : (k1_funct_1(sK6,sK7) != k1_funct_1(sK6,X0) | sK8 = X0 | ~r2_hidden(sK8,k1_relat_1(sK6)) | ~r2_hidden(X0,k1_relat_1(sK6))) ) | (~spl11_3 | ~spl11_7)),
% 0.22/0.58    inference(subsumption_resolution,[],[f196,f117])).
% 0.22/0.58  fof(f117,plain,(
% 0.22/0.58    sP0(sK6) | ~spl11_7),
% 0.22/0.58    inference(avatar_component_clause,[],[f115])).
% 0.22/0.58  fof(f196,plain,(
% 0.22/0.58    ( ! [X0] : (k1_funct_1(sK6,sK7) != k1_funct_1(sK6,X0) | sK8 = X0 | ~r2_hidden(sK8,k1_relat_1(sK6)) | ~r2_hidden(X0,k1_relat_1(sK6)) | ~sP0(sK6)) ) | ~spl11_3),
% 0.22/0.58    inference(superposition,[],[f53,f86])).
% 0.22/0.58  fof(f86,plain,(
% 0.22/0.58    k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8) | ~spl11_3),
% 0.22/0.58    inference(avatar_component_clause,[],[f84])).
% 0.22/0.58  fof(f84,plain,(
% 0.22/0.58    spl11_3 <=> k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 0.22/0.58  fof(f53,plain,(
% 0.22/0.58    ( ! [X4,X0,X3] : (k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | X3 = X4 | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~sP0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f36])).
% 0.22/0.58  fof(f36,plain,(
% 0.22/0.58    ! [X0] : ((sP0(X0) | (sK9(X0) != sK10(X0) & k1_funct_1(X0,sK9(X0)) = k1_funct_1(X0,sK10(X0)) & r2_hidden(sK10(X0),k1_relat_1(X0)) & r2_hidden(sK9(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f34,f35])).
% 0.22/0.58  fof(f35,plain,(
% 0.22/0.58    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK9(X0) != sK10(X0) & k1_funct_1(X0,sK9(X0)) = k1_funct_1(X0,sK10(X0)) & r2_hidden(sK10(X0),k1_relat_1(X0)) & r2_hidden(sK9(X0),k1_relat_1(X0))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f34,plain,(
% 0.22/0.58    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.22/0.58    inference(rectify,[],[f33])).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.22/0.58    inference(nnf_transformation,[],[f19])).
% 0.22/0.58  fof(f194,plain,(
% 0.22/0.58    spl11_1 | ~spl11_7),
% 0.22/0.58    inference(avatar_split_clause,[],[f161,f115,f75])).
% 0.22/0.58  fof(f161,plain,(
% 0.22/0.58    v2_funct_1(sK6) | ~spl11_7),
% 0.22/0.58    inference(subsumption_resolution,[],[f160,f42])).
% 0.22/0.58  fof(f160,plain,(
% 0.22/0.58    ~v1_funct_1(sK6) | v2_funct_1(sK6) | ~spl11_7),
% 0.22/0.58    inference(subsumption_resolution,[],[f159,f107])).
% 0.22/0.58  fof(f159,plain,(
% 0.22/0.58    ~v1_relat_1(sK6) | ~v1_funct_1(sK6) | v2_funct_1(sK6) | ~spl11_7),
% 0.22/0.58    inference(resolution,[],[f117,f102])).
% 0.22/0.58  fof(f102,plain,(
% 0.22/0.58    ( ! [X0] : (~sP0(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | v2_funct_1(X0)) )),
% 0.22/0.58    inference(resolution,[],[f58,f52])).
% 0.22/0.58  fof(f52,plain,(
% 0.22/0.58    ( ! [X0] : (~sP1(X0) | ~sP0(X0) | v2_funct_1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f32])).
% 0.22/0.58  fof(f193,plain,(
% 0.22/0.58    spl11_7 | ~spl11_9 | ~spl11_12),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f192])).
% 0.22/0.58  fof(f192,plain,(
% 0.22/0.58    $false | (spl11_7 | ~spl11_9 | ~spl11_12)),
% 0.22/0.58    inference(subsumption_resolution,[],[f191,f116])).
% 0.22/0.58  fof(f191,plain,(
% 0.22/0.58    sP0(sK6) | (~spl11_9 | ~spl11_12)),
% 0.22/0.58    inference(trivial_inequality_removal,[],[f189])).
% 0.22/0.58  fof(f189,plain,(
% 0.22/0.58    sK9(sK6) != sK9(sK6) | sP0(sK6) | (~spl11_9 | ~spl11_12)),
% 0.22/0.58    inference(superposition,[],[f57,f186])).
% 0.22/0.58  fof(f186,plain,(
% 0.22/0.58    sK10(sK6) = sK9(sK6) | (~spl11_9 | ~spl11_12)),
% 0.22/0.58    inference(subsumption_resolution,[],[f185,f157])).
% 0.22/0.58  fof(f157,plain,(
% 0.22/0.58    r2_hidden(sK9(sK6),sK5) | ~spl11_12),
% 0.22/0.58    inference(avatar_component_clause,[],[f155])).
% 0.22/0.58  fof(f155,plain,(
% 0.22/0.58    spl11_12 <=> r2_hidden(sK9(sK6),sK5)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 0.22/0.58  fof(f185,plain,(
% 0.22/0.58    sK10(sK6) = sK9(sK6) | ~r2_hidden(sK9(sK6),sK5) | ~spl11_9),
% 0.22/0.58    inference(equality_resolution,[],[f124])).
% 0.22/0.58  fof(f124,plain,(
% 0.22/0.58    ( ! [X0] : (k1_funct_1(sK6,X0) != k1_funct_1(sK6,sK9(sK6)) | sK10(sK6) = X0 | ~r2_hidden(X0,sK5)) ) | ~spl11_9),
% 0.22/0.58    inference(avatar_component_clause,[],[f123])).
% 0.22/0.58  fof(f123,plain,(
% 0.22/0.58    spl11_9 <=> ! [X0] : (k1_funct_1(sK6,X0) != k1_funct_1(sK6,sK9(sK6)) | sK10(sK6) = X0 | ~r2_hidden(X0,sK5))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 0.22/0.58  fof(f57,plain,(
% 0.22/0.58    ( ! [X0] : (sK9(X0) != sK10(X0) | sP0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f36])).
% 0.22/0.58  fof(f179,plain,(
% 0.22/0.58    spl11_12 | spl11_7 | ~spl11_10),
% 0.22/0.58    inference(avatar_split_clause,[],[f178,f142,f115,f155])).
% 0.22/0.58  fof(f178,plain,(
% 0.22/0.58    r2_hidden(sK9(sK6),sK5) | (spl11_7 | ~spl11_10)),
% 0.22/0.58    inference(subsumption_resolution,[],[f177,f116])).
% 0.22/0.58  fof(f177,plain,(
% 0.22/0.58    r2_hidden(sK9(sK6),sK5) | sP0(sK6) | ~spl11_10),
% 0.22/0.58    inference(superposition,[],[f54,f144])).
% 0.22/0.58  fof(f54,plain,(
% 0.22/0.58    ( ! [X0] : (r2_hidden(sK9(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f36])).
% 0.22/0.58  fof(f175,plain,(
% 0.22/0.58    ~spl11_11),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f174])).
% 0.22/0.58  fof(f174,plain,(
% 0.22/0.58    $false | ~spl11_11),
% 0.22/0.58    inference(subsumption_resolution,[],[f172,f73])).
% 0.22/0.58  fof(f73,plain,(
% 0.22/0.58    ( ! [X1] : (~sP2(k1_xboole_0,X1)) )),
% 0.22/0.58    inference(equality_resolution,[],[f66])).
% 0.22/0.58  fof(f66,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP2(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f41])).
% 0.22/0.58  fof(f41,plain,(
% 0.22/0.58    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP2(X0,X1))),
% 0.22/0.58    inference(nnf_transformation,[],[f22])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP2(X0,X1))),
% 0.22/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.58  fof(f172,plain,(
% 0.22/0.58    sP2(k1_xboole_0,k1_xboole_0) | ~spl11_11),
% 0.22/0.58    inference(backward_demodulation,[],[f148,f165])).
% 0.22/0.58  fof(f165,plain,(
% 0.22/0.58    k1_xboole_0 = sK5 | ~spl11_11),
% 0.22/0.58    inference(resolution,[],[f148,f65])).
% 0.22/0.58  fof(f65,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~sP2(X0,X1) | k1_xboole_0 = X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f41])).
% 0.22/0.58  fof(f148,plain,(
% 0.22/0.58    sP2(sK5,sK5) | ~spl11_11),
% 0.22/0.58    inference(avatar_component_clause,[],[f146])).
% 0.22/0.58  fof(f146,plain,(
% 0.22/0.58    spl11_11 <=> sP2(sK5,sK5)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 0.22/0.58  fof(f153,plain,(
% 0.22/0.58    spl11_7 | spl11_8 | ~spl11_10),
% 0.22/0.58    inference(avatar_split_clause,[],[f152,f142,f119,f115])).
% 0.22/0.58  fof(f119,plain,(
% 0.22/0.58    spl11_8 <=> r2_hidden(sK10(sK6),sK5)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 0.22/0.58  fof(f152,plain,(
% 0.22/0.58    sP0(sK6) | (spl11_8 | ~spl11_10)),
% 0.22/0.58    inference(subsumption_resolution,[],[f150,f121])).
% 0.22/0.58  fof(f121,plain,(
% 0.22/0.58    ~r2_hidden(sK10(sK6),sK5) | spl11_8),
% 0.22/0.58    inference(avatar_component_clause,[],[f119])).
% 0.22/0.58  fof(f150,plain,(
% 0.22/0.58    r2_hidden(sK10(sK6),sK5) | sP0(sK6) | ~spl11_10),
% 0.22/0.58    inference(superposition,[],[f55,f144])).
% 0.22/0.58  fof(f55,plain,(
% 0.22/0.58    ( ! [X0] : (r2_hidden(sK10(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f36])).
% 0.22/0.58  fof(f149,plain,(
% 0.22/0.58    spl11_10 | spl11_11),
% 0.22/0.58    inference(avatar_split_clause,[],[f140,f146,f142])).
% 0.22/0.58  fof(f140,plain,(
% 0.22/0.58    sP2(sK5,sK5) | sK5 = k1_relat_1(sK6)),
% 0.22/0.58    inference(subsumption_resolution,[],[f139,f43])).
% 0.22/0.58  fof(f43,plain,(
% 0.22/0.58    v1_funct_2(sK6,sK5,sK5)),
% 0.22/0.58    inference(cnf_transformation,[],[f31])).
% 0.22/0.58  fof(f139,plain,(
% 0.22/0.58    ~v1_funct_2(sK6,sK5,sK5) | sP2(sK5,sK5) | sK5 = k1_relat_1(sK6)),
% 0.22/0.58    inference(resolution,[],[f129,f44])).
% 0.22/0.58  fof(f129,plain,(
% 0.22/0.58    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP2(X3,X4) | k1_relat_1(X5) = X3) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f127,f67])).
% 0.22/0.58  fof(f67,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP3(X0,X2,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f25])).
% 0.22/0.58  fof(f25,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((sP4(X2,X1,X0) & sP3(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(definition_folding,[],[f16,f24,f23,f22])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP2(X0,X1) | ~sP3(X0,X2,X1))),
% 0.22/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP4(X2,X1,X0))),
% 0.22/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.22/0.58  fof(f16,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(flattening,[],[f15])).
% 0.22/0.58  fof(f15,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(ennf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.58  fof(f127,plain,(
% 0.22/0.58    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP2(X3,X4) | ~sP3(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.22/0.58    inference(superposition,[],[f63,f60])).
% 0.22/0.58  fof(f60,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f14])).
% 0.22/0.58  fof(f14,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(ennf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.58  fof(f63,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP2(X0,X2) | ~sP3(X0,X1,X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f40])).
% 0.22/0.58  fof(f40,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP2(X0,X2) | ~sP3(X0,X1,X2))),
% 0.22/0.58    inference(rectify,[],[f39])).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP2(X0,X1) | ~sP3(X0,X2,X1))),
% 0.22/0.58    inference(nnf_transformation,[],[f23])).
% 0.22/0.58  fof(f126,plain,(
% 0.22/0.58    spl11_7 | ~spl11_8 | spl11_9 | ~spl11_6),
% 0.22/0.58    inference(avatar_split_clause,[],[f113,f99,f123,f119,f115])).
% 0.22/0.58  fof(f99,plain,(
% 0.22/0.58    spl11_6 <=> ! [X5,X4] : (X4 = X5 | ~r2_hidden(X4,sK5) | ~r2_hidden(X5,sK5) | k1_funct_1(sK6,X4) != k1_funct_1(sK6,X5))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 0.22/0.58  fof(f113,plain,(
% 0.22/0.58    ( ! [X1] : (k1_funct_1(sK6,X1) != k1_funct_1(sK6,sK9(sK6)) | ~r2_hidden(sK10(sK6),sK5) | ~r2_hidden(X1,sK5) | sK10(sK6) = X1 | sP0(sK6)) ) | ~spl11_6),
% 0.22/0.58    inference(superposition,[],[f100,f56])).
% 0.22/0.58  fof(f56,plain,(
% 0.22/0.58    ( ! [X0] : (k1_funct_1(X0,sK9(X0)) = k1_funct_1(X0,sK10(X0)) | sP0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f36])).
% 0.22/0.58  fof(f100,plain,(
% 0.22/0.58    ( ! [X4,X5] : (k1_funct_1(sK6,X4) != k1_funct_1(sK6,X5) | ~r2_hidden(X4,sK5) | ~r2_hidden(X5,sK5) | X4 = X5) ) | ~spl11_6),
% 0.22/0.58    inference(avatar_component_clause,[],[f99])).
% 0.22/0.58  fof(f101,plain,(
% 0.22/0.58    spl11_1 | spl11_6),
% 0.22/0.58    inference(avatar_split_clause,[],[f45,f99,f75])).
% 0.22/0.58  fof(f45,plain,(
% 0.22/0.58    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK6,X4) != k1_funct_1(sK6,X5) | ~r2_hidden(X5,sK5) | ~r2_hidden(X4,sK5) | v2_funct_1(sK6)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f31])).
% 0.22/0.58  fof(f97,plain,(
% 0.22/0.58    ~spl11_1 | spl11_5),
% 0.22/0.58    inference(avatar_split_clause,[],[f46,f94,f75])).
% 0.22/0.58  % (11953)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.58  fof(f46,plain,(
% 0.22/0.58    r2_hidden(sK7,sK5) | ~v2_funct_1(sK6)),
% 0.22/0.58    inference(cnf_transformation,[],[f31])).
% 0.22/0.58  fof(f92,plain,(
% 0.22/0.58    ~spl11_1 | spl11_4),
% 0.22/0.58    inference(avatar_split_clause,[],[f47,f89,f75])).
% 0.22/0.58  fof(f47,plain,(
% 0.22/0.58    r2_hidden(sK8,sK5) | ~v2_funct_1(sK6)),
% 0.22/0.58    inference(cnf_transformation,[],[f31])).
% 0.22/0.58  fof(f87,plain,(
% 0.22/0.58    ~spl11_1 | spl11_3),
% 0.22/0.58    inference(avatar_split_clause,[],[f48,f84,f75])).
% 0.22/0.58  fof(f48,plain,(
% 0.22/0.58    k1_funct_1(sK6,sK7) = k1_funct_1(sK6,sK8) | ~v2_funct_1(sK6)),
% 0.22/0.58    inference(cnf_transformation,[],[f31])).
% 0.22/0.58  fof(f82,plain,(
% 0.22/0.58    ~spl11_1 | ~spl11_2),
% 0.22/0.58    inference(avatar_split_clause,[],[f49,f79,f75])).
% 0.22/0.58  fof(f49,plain,(
% 0.22/0.58    sK7 != sK8 | ~v2_funct_1(sK6)),
% 0.22/0.58    inference(cnf_transformation,[],[f31])).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (11932)------------------------------
% 0.22/0.58  % (11932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (11932)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (11932)Memory used [KB]: 6268
% 0.22/0.58  % (11932)Time elapsed: 0.117 s
% 0.22/0.58  % (11932)------------------------------
% 0.22/0.58  % (11932)------------------------------
% 0.22/0.58  % (11927)Success in time 0.212 s
%------------------------------------------------------------------------------
