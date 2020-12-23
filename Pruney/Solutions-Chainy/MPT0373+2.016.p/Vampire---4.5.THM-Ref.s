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
% DateTime   : Thu Dec  3 12:45:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 156 expanded)
%              Number of leaves         :   28 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  216 ( 359 expanded)
%              Number of equality atoms :   35 (  70 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f75,f79,f88,f102,f108,f132,f136,f142,f148,f158])).

fof(f158,plain,(
    ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl3_4 ),
    inference(resolution,[],[f84,f37])).

fof(f37,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f84,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_4
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f148,plain,(
    ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | ~ spl3_6 ),
    inference(resolution,[],[f98,f37])).

fof(f98,plain,
    ( v1_xboole_0(k1_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_6
  <=> v1_xboole_0(k1_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f142,plain,
    ( spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f140,f121,f73])).

fof(f73,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f121,plain,
    ( spl3_11
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f140,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_11 ),
    inference(resolution,[],[f122,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

% (19439)Refutation not found, incomplete strategy% (19439)------------------------------
% (19439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19439)Termination reason: Refutation not found, incomplete strategy

% (19439)Memory used [KB]: 10618
% (19439)Time elapsed: 0.120 s
% (19439)------------------------------
% (19439)------------------------------
fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f122,plain,
    ( v1_xboole_0(sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f136,plain,
    ( spl3_11
    | ~ spl3_3
    | spl3_13 ),
    inference(avatar_split_clause,[],[f134,f130,f77,f121])).

fof(f77,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f130,plain,
    ( spl3_13
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f134,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0)
    | spl3_13 ),
    inference(resolution,[],[f131,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f131,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f130])).

fof(f132,plain,
    ( ~ spl3_13
    | spl3_8 ),
    inference(avatar_split_clause,[],[f128,f106,f130])).

fof(f106,plain,
    ( spl3_8
  <=> r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f128,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl3_8 ),
    inference(resolution,[],[f66,f107])).

fof(f107,plain,
    ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f64])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f56,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f57,f58])).

% (19433)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

% (19437)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f108,plain,
    ( ~ spl3_8
    | spl3_7 ),
    inference(avatar_split_clause,[],[f103,f100,f106])).

fof(f100,plain,
    ( spl3_7
  <=> r1_tarski(k1_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f103,plain,
    ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)
    | spl3_7 ),
    inference(resolution,[],[f101,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f101,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k1_zfmisc_1(sK0))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f102,plain,
    ( spl3_6
    | ~ spl3_7
    | spl3_5 ),
    inference(avatar_split_clause,[],[f93,f86,f100,f97])).

fof(f86,plain,
    ( spl3_5
  <=> r2_hidden(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f93,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | spl3_5 ),
    inference(resolution,[],[f92,f80])).

fof(f80,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f39,f38])).

fof(f38,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f92,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X2)
        | ~ r1_tarski(X2,k1_zfmisc_1(sK0))
        | v1_xboole_0(X2) )
    | spl3_5 ),
    inference(resolution,[],[f90,f43])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)
        | ~ r1_tarski(X0,k1_zfmisc_1(sK0)) )
    | spl3_5 ),
    inference(resolution,[],[f48,f87])).

fof(f87,plain,
    ( ~ r2_hidden(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

% (19459)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f88,plain,
    ( spl3_4
    | ~ spl3_5
    | spl3_1 ),
    inference(avatar_split_clause,[],[f81,f69,f86,f83])).

fof(f69,plain,
    ( spl3_1
  <=> m1_subset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f81,plain,
    ( ~ r2_hidden(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | spl3_1 ),
    inference(resolution,[],[f44,f70])).

fof(f70,plain,
    ( ~ m1_subset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f34,f77])).

fof(f34,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0
    & m1_subset_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        & k1_xboole_0 != X0
        & m1_subset_1(X1,X0) )
   => ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
      & k1_xboole_0 != sK0
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      & k1_xboole_0 != X0
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      & k1_xboole_0 != X0
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ( k1_xboole_0 != X0
         => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

fof(f75,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f35,f73])).

fof(f35,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f65,f69])).

fof(f65,plain,(
    ~ m1_subset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0)) ),
    inference(definition_unfolding,[],[f36,f64])).

fof(f36,plain,(
    ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:19:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (19439)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (19431)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (19449)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (19457)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (19453)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (19449)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (19450)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (19445)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (19432)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f71,f75,f79,f88,f102,f108,f132,f136,f142,f148,f158])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ~spl3_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f153])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    $false | ~spl3_4),
% 0.21/0.52    inference(resolution,[],[f84,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,axiom,(
% 0.21/0.52    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    spl3_4 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    ~spl3_6),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f143])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    $false | ~spl3_6),
% 0.21/0.52    inference(resolution,[],[f98,f37])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    v1_xboole_0(k1_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | ~spl3_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    spl3_6 <=> v1_xboole_0(k1_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    spl3_2 | ~spl3_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f140,f121,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl3_2 <=> k1_xboole_0 = sK0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    spl3_11 <=> v1_xboole_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | ~spl3_11),
% 0.21/0.52    inference(resolution,[],[f122,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  % (19439)Refutation not found, incomplete strategy% (19439)------------------------------
% 0.21/0.52  % (19439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19439)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19439)Memory used [KB]: 10618
% 0.21/0.52  % (19439)Time elapsed: 0.120 s
% 0.21/0.52  % (19439)------------------------------
% 0.21/0.52  % (19439)------------------------------
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    v1_xboole_0(sK0) | ~spl3_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f121])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    spl3_11 | ~spl3_3 | spl3_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f134,f130,f77,f121])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    spl3_3 <=> m1_subset_1(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    spl3_13 <=> r2_hidden(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0) | spl3_13),
% 0.21/0.52    inference(resolution,[],[f131,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    ~r2_hidden(sK1,sK0) | spl3_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f130])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    ~spl3_13 | spl3_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f128,f106,f130])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    spl3_8 <=> r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    ~r2_hidden(sK1,sK0) | spl3_8),
% 0.21/0.52    inference(resolution,[],[f66,f107])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ~r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) | spl3_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f106])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f52,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f40,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f42,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f54,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f55,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f56,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f57,f58])).
% 0.21/0.52  % (19433)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.52  % (19437)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ~spl3_8 | spl3_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f103,f100,f106])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    spl3_7 <=> r1_tarski(k1_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k1_zfmisc_1(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ~r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) | spl3_7),
% 0.21/0.53    inference(resolution,[],[f101,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    ~r1_tarski(k1_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k1_zfmisc_1(sK0)) | spl3_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f100])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    spl3_6 | ~spl3_7 | spl3_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f93,f86,f100,f97])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    spl3_5 <=> r2_hidden(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ~r1_tarski(k1_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | spl3_5),
% 0.21/0.53    inference(resolution,[],[f92,f80])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f39,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    ( ! [X2] : (~m1_subset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X2) | ~r1_tarski(X2,k1_zfmisc_1(sK0)) | v1_xboole_0(X2)) ) | spl3_5),
% 0.21/0.53    inference(resolution,[],[f90,f43])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) | ~r1_tarski(X0,k1_zfmisc_1(sK0))) ) | spl3_5),
% 0.21/0.53    inference(resolution,[],[f48,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ~r2_hidden(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0)) | spl3_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f86])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f29])).
% 0.21/0.53  % (19459)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    spl3_4 | ~spl3_5 | spl3_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f81,f69,f86,f83])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    spl3_1 <=> m1_subset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ~r2_hidden(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | spl3_1),
% 0.21/0.53    inference(resolution,[],[f44,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ~m1_subset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0)) | spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f69])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    spl3_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f34,f77])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    m1_subset_1(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(sK1,sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ? [X0,X1] : (~m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X1,X0)) => (~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(sK1,sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X0,X1] : (~m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X1,X0))),
% 0.21/0.53    inference(flattening,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0,X1] : ((~m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X1,X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.21/0.53    inference(negated_conjecture,[],[f17])).
% 0.21/0.53  fof(f17,conjecture,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ~spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f35,f73])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    k1_xboole_0 != sK0),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ~spl3_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f65,f69])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ~m1_subset_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(definition_unfolding,[],[f36,f64])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (19449)------------------------------
% 0.21/0.53  % (19449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19449)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (19449)Memory used [KB]: 10746
% 0.21/0.53  % (19449)Time elapsed: 0.105 s
% 0.21/0.53  % (19449)------------------------------
% 0.21/0.53  % (19449)------------------------------
% 0.21/0.53  % (19428)Success in time 0.165 s
%------------------------------------------------------------------------------
