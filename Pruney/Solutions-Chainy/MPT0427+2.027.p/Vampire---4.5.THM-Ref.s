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
% DateTime   : Thu Dec  3 12:46:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 217 expanded)
%              Number of leaves         :   28 (  89 expanded)
%              Depth                    :    9
%              Number of atoms          :  303 ( 589 expanded)
%              Number of equality atoms :   58 ( 117 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f389,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f55,f60,f93,f105,f110,f131,f177,f217,f233,f238,f253,f297,f309,f311,f349,f355,f388])).

fof(f388,plain,
    ( spl3_31
    | ~ spl3_33 ),
    inference(avatar_contradiction_clause,[],[f387])).

fof(f387,plain,
    ( $false
    | spl3_31
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f385,f296])).

fof(f296,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | spl3_31 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl3_31
  <=> r1_tarski(k1_setfam_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f385,plain,
    ( r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ spl3_33 ),
    inference(resolution,[],[f308,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f308,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl3_33
  <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f355,plain,
    ( ~ spl3_1
    | spl3_13
    | spl3_34 ),
    inference(avatar_contradiction_clause,[],[f354])).

fof(f354,plain,
    ( $false
    | ~ spl3_1
    | spl3_13
    | spl3_34 ),
    inference(subsumption_resolution,[],[f353,f44])).

fof(f44,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f353,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_13
    | spl3_34 ),
    inference(subsumption_resolution,[],[f351,f125])).

fof(f125,plain,
    ( k1_xboole_0 != sK1
    | spl3_13 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl3_13
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f351,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | spl3_34 ),
    inference(resolution,[],[f348,f28])).

% (17102)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f348,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl3_34 ),
    inference(avatar_component_clause,[],[f346])).

fof(f346,plain,
    ( spl3_34
  <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f349,plain,
    ( ~ spl3_34
    | ~ spl3_25
    | spl3_26 ),
    inference(avatar_split_clause,[],[f315,f250,f214,f346])).

fof(f214,plain,
    ( spl3_25
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f250,plain,
    ( spl3_26
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f315,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | ~ spl3_25
    | spl3_26 ),
    inference(forward_demodulation,[],[f252,f216])).

fof(f216,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f214])).

fof(f252,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f250])).

fof(f311,plain,
    ( sK1 != sK2
    | k8_setfam_1(sK0,sK1) != k1_setfam_1(sK1)
    | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f309,plain,
    ( spl3_33
    | ~ spl3_3
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f292,f214,f52,f306])).

fof(f52,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f292,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl3_3
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f291,f54])).

% (17110)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
fof(f54,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f291,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_25 ),
    inference(superposition,[],[f30,f216])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f297,plain,
    ( ~ spl3_31
    | spl3_18
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f290,f214,f174,f294])).

fof(f174,plain,
    ( spl3_18
  <=> r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f290,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | spl3_18
    | ~ spl3_25 ),
    inference(backward_demodulation,[],[f176,f216])).

fof(f176,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f174])).

fof(f253,plain,
    ( ~ spl3_26
    | spl3_4
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f245,f128,f57,f250])).

fof(f57,plain,
    ( spl3_4
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f128,plain,
    ( spl3_14
  <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f245,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1))
    | spl3_4
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f59,f130])).

fof(f130,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f128])).

fof(f59,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f238,plain,
    ( spl3_18
    | ~ spl3_24 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | spl3_18
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f236,f39])).

fof(f39,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f236,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_18
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f230,f79])).

fof(f79,plain,(
    ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f78,f27])).

fof(f27,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f78,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f38,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f230,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0)
    | spl3_18
    | ~ spl3_24 ),
    inference(backward_demodulation,[],[f176,f212])).

fof(f212,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl3_24
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f233,plain,
    ( spl3_8
    | ~ spl3_24 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | spl3_8
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f227,f27])).

fof(f227,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl3_8
    | ~ spl3_24 ),
    inference(backward_demodulation,[],[f92,f212])).

fof(f92,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_8
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f217,plain,
    ( spl3_24
    | spl3_25
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f199,f107,f52,f214,f210])).

fof(f107,plain,
    ( spl3_10
  <=> k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f199,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f98,f109])).

fof(f109,plain,
    ( k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f107])).

fof(f98,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f31,f54])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f177,plain,
    ( ~ spl3_18
    | spl3_4
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f167,f124,f57,f174])).

fof(f167,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | spl3_4
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f166,f79])).

fof(f166,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_4
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f59,f126])).

fof(f126,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f124])).

fof(f131,plain,
    ( spl3_13
    | spl3_14
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f113,f102,f47,f128,f124])).

fof(f47,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f102,plain,
    ( spl3_9
  <=> k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f113,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | k1_xboole_0 = sK1
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f97,f104])).

fof(f104,plain,
    ( k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f102])).

fof(f97,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f31,f49])).

fof(f49,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f110,plain,
    ( spl3_10
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f83,f52,f107])).

fof(f83,plain,
    ( k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f29,f54])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f105,plain,
    ( spl3_9
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f82,f47,f102])).

fof(f82,plain,
    ( k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f29,f49])).

fof(f93,plain,
    ( spl3_7
    | ~ spl3_8
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f74,f42,f90,f86])).

fof(f86,plain,
    ( spl3_7
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f74,plain,
    ( ~ r1_tarski(sK2,sK1)
    | sK1 = sK2
    | ~ spl3_1 ),
    inference(resolution,[],[f35,f44])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f26,f57])).

fof(f26,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
          & r1_tarski(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f55,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f25,f42])).

fof(f25,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:36:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (17097)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (17087)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (17098)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  % (17104)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (17097)Refutation not found, incomplete strategy% (17097)------------------------------
% 0.20/0.51  % (17097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (17090)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (17097)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (17097)Memory used [KB]: 10490
% 0.20/0.51  % (17097)Time elapsed: 0.079 s
% 0.20/0.51  % (17097)------------------------------
% 0.20/0.51  % (17097)------------------------------
% 0.20/0.51  % (17087)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f389,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f45,f50,f55,f60,f93,f105,f110,f131,f177,f217,f233,f238,f253,f297,f309,f311,f349,f355,f388])).
% 0.20/0.51  fof(f388,plain,(
% 0.20/0.51    spl3_31 | ~spl3_33),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f387])).
% 0.20/0.51  fof(f387,plain,(
% 0.20/0.51    $false | (spl3_31 | ~spl3_33)),
% 0.20/0.51    inference(subsumption_resolution,[],[f385,f296])).
% 0.20/0.51  fof(f296,plain,(
% 0.20/0.51    ~r1_tarski(k1_setfam_1(sK2),sK0) | spl3_31),
% 0.20/0.51    inference(avatar_component_clause,[],[f294])).
% 0.20/0.51  fof(f294,plain,(
% 0.20/0.51    spl3_31 <=> r1_tarski(k1_setfam_1(sK2),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.51  fof(f385,plain,(
% 0.20/0.51    r1_tarski(k1_setfam_1(sK2),sK0) | ~spl3_33),
% 0.20/0.51    inference(resolution,[],[f308,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.51    inference(nnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.51  fof(f308,plain,(
% 0.20/0.51    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~spl3_33),
% 0.20/0.51    inference(avatar_component_clause,[],[f306])).
% 0.20/0.51  fof(f306,plain,(
% 0.20/0.51    spl3_33 <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.20/0.51  fof(f355,plain,(
% 0.20/0.51    ~spl3_1 | spl3_13 | spl3_34),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f354])).
% 0.20/0.51  fof(f354,plain,(
% 0.20/0.51    $false | (~spl3_1 | spl3_13 | spl3_34)),
% 0.20/0.51    inference(subsumption_resolution,[],[f353,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    r1_tarski(sK1,sK2) | ~spl3_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    spl3_1 <=> r1_tarski(sK1,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.51  fof(f353,plain,(
% 0.20/0.51    ~r1_tarski(sK1,sK2) | (spl3_13 | spl3_34)),
% 0.20/0.51    inference(subsumption_resolution,[],[f351,f125])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    k1_xboole_0 != sK1 | spl3_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f124])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    spl3_13 <=> k1_xboole_0 = sK1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.51  fof(f351,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | spl3_34),
% 0.20/0.51    inference(resolution,[],[f348,f28])).
% 0.20/0.51  % (17102)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(flattening,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.20/0.51  fof(f348,plain,(
% 0.20/0.51    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | spl3_34),
% 0.20/0.51    inference(avatar_component_clause,[],[f346])).
% 0.20/0.51  fof(f346,plain,(
% 0.20/0.51    spl3_34 <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.20/0.51  fof(f349,plain,(
% 0.20/0.51    ~spl3_34 | ~spl3_25 | spl3_26),
% 0.20/0.51    inference(avatar_split_clause,[],[f315,f250,f214,f346])).
% 0.20/0.51  fof(f214,plain,(
% 0.20/0.51    spl3_25 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.51  fof(f250,plain,(
% 0.20/0.51    spl3_26 <=> r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.51  fof(f315,plain,(
% 0.20/0.51    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (~spl3_25 | spl3_26)),
% 0.20/0.51    inference(forward_demodulation,[],[f252,f216])).
% 0.20/0.51  fof(f216,plain,(
% 0.20/0.51    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_25),
% 0.20/0.51    inference(avatar_component_clause,[],[f214])).
% 0.20/0.51  fof(f252,plain,(
% 0.20/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) | spl3_26),
% 0.20/0.51    inference(avatar_component_clause,[],[f250])).
% 0.20/0.51  fof(f311,plain,(
% 0.20/0.51    sK1 != sK2 | k8_setfam_1(sK0,sK1) != k1_setfam_1(sK1) | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f309,plain,(
% 0.20/0.51    spl3_33 | ~spl3_3 | ~spl3_25),
% 0.20/0.51    inference(avatar_split_clause,[],[f292,f214,f52,f306])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.51  fof(f292,plain,(
% 0.20/0.51    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | (~spl3_3 | ~spl3_25)),
% 0.20/0.51    inference(subsumption_resolution,[],[f291,f54])).
% 0.20/0.51  % (17110)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f52])).
% 0.20/0.51  fof(f291,plain,(
% 0.20/0.51    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_25),
% 0.20/0.51    inference(superposition,[],[f30,f216])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.20/0.51  fof(f297,plain,(
% 0.20/0.51    ~spl3_31 | spl3_18 | ~spl3_25),
% 0.20/0.51    inference(avatar_split_clause,[],[f290,f214,f174,f294])).
% 0.20/0.51  fof(f174,plain,(
% 0.20/0.51    spl3_18 <=> r1_tarski(k8_setfam_1(sK0,sK2),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.51  fof(f290,plain,(
% 0.20/0.51    ~r1_tarski(k1_setfam_1(sK2),sK0) | (spl3_18 | ~spl3_25)),
% 0.20/0.51    inference(backward_demodulation,[],[f176,f216])).
% 0.20/0.51  fof(f176,plain,(
% 0.20/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0) | spl3_18),
% 0.20/0.51    inference(avatar_component_clause,[],[f174])).
% 0.20/0.51  fof(f253,plain,(
% 0.20/0.51    ~spl3_26 | spl3_4 | ~spl3_14),
% 0.20/0.51    inference(avatar_split_clause,[],[f245,f128,f57,f250])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    spl3_4 <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    spl3_14 <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.51  fof(f245,plain,(
% 0.20/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) | (spl3_4 | ~spl3_14)),
% 0.20/0.51    inference(backward_demodulation,[],[f59,f130])).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_14),
% 0.20/0.51    inference(avatar_component_clause,[],[f128])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) | spl3_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f57])).
% 0.20/0.51  fof(f238,plain,(
% 0.20/0.51    spl3_18 | ~spl3_24),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f237])).
% 0.20/0.51  fof(f237,plain,(
% 0.20/0.51    $false | (spl3_18 | ~spl3_24)),
% 0.20/0.51    inference(subsumption_resolution,[],[f236,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(flattening,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.51  fof(f236,plain,(
% 0.20/0.51    ~r1_tarski(sK0,sK0) | (spl3_18 | ~spl3_24)),
% 0.20/0.51    inference(forward_demodulation,[],[f230,f79])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f78,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~r1_tarski(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(resolution,[],[f38,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.20/0.51    inference(equality_resolution,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.20/0.51  fof(f230,plain,(
% 0.20/0.51    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0) | (spl3_18 | ~spl3_24)),
% 0.20/0.51    inference(backward_demodulation,[],[f176,f212])).
% 0.20/0.51  fof(f212,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | ~spl3_24),
% 0.20/0.51    inference(avatar_component_clause,[],[f210])).
% 0.20/0.51  fof(f210,plain,(
% 0.20/0.51    spl3_24 <=> k1_xboole_0 = sK2),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.51  fof(f233,plain,(
% 0.20/0.51    spl3_8 | ~spl3_24),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f232])).
% 0.20/0.51  fof(f232,plain,(
% 0.20/0.51    $false | (spl3_8 | ~spl3_24)),
% 0.20/0.51    inference(subsumption_resolution,[],[f227,f27])).
% 0.20/0.51  fof(f227,plain,(
% 0.20/0.51    ~r1_tarski(k1_xboole_0,sK1) | (spl3_8 | ~spl3_24)),
% 0.20/0.51    inference(backward_demodulation,[],[f92,f212])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    ~r1_tarski(sK2,sK1) | spl3_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    spl3_8 <=> r1_tarski(sK2,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.51  fof(f217,plain,(
% 0.20/0.51    spl3_24 | spl3_25 | ~spl3_3 | ~spl3_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f199,f107,f52,f214,f210])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    spl3_10 <=> k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.51  fof(f199,plain,(
% 0.20/0.51    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | k1_xboole_0 = sK2 | (~spl3_3 | ~spl3_10)),
% 0.20/0.51    inference(forward_demodulation,[],[f98,f109])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f107])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) | ~spl3_3),
% 0.20/0.51    inference(resolution,[],[f31,f54])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f177,plain,(
% 0.20/0.51    ~spl3_18 | spl3_4 | ~spl3_13),
% 0.20/0.51    inference(avatar_split_clause,[],[f167,f124,f57,f174])).
% 0.20/0.51  fof(f167,plain,(
% 0.20/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0) | (spl3_4 | ~spl3_13)),
% 0.20/0.51    inference(forward_demodulation,[],[f166,f79])).
% 0.20/0.51  fof(f166,plain,(
% 0.20/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | (spl3_4 | ~spl3_13)),
% 0.20/0.51    inference(forward_demodulation,[],[f59,f126])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | ~spl3_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f124])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    spl3_13 | spl3_14 | ~spl3_2 | ~spl3_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f113,f102,f47,f128,f124])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    spl3_9 <=> k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | k1_xboole_0 = sK1 | (~spl3_2 | ~spl3_9)),
% 0.20/0.51    inference(forward_demodulation,[],[f97,f104])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f102])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) | ~spl3_2),
% 0.20/0.51    inference(resolution,[],[f31,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f47])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    spl3_10 | ~spl3_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f83,f52,f107])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_3),
% 0.20/0.51    inference(resolution,[],[f29,f54])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    spl3_9 | ~spl3_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f82,f47,f102])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_2),
% 0.20/0.51    inference(resolution,[],[f29,f49])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    spl3_7 | ~spl3_8 | ~spl3_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f74,f42,f90,f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    spl3_7 <=> sK1 = sK2),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ~r1_tarski(sK2,sK1) | sK1 = sK2 | ~spl3_1),
% 0.20/0.51    inference(resolution,[],[f35,f44])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ~spl3_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f26,f57])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18,f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.51    inference(flattening,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.20/0.51    inference(negated_conjecture,[],[f8])).
% 0.20/0.51  fof(f8,conjecture,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    spl3_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f24,f52])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    spl3_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f23,f47])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    spl3_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f25,f42])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    r1_tarski(sK1,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (17087)------------------------------
% 0.20/0.51  % (17087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (17087)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (17087)Memory used [KB]: 6268
% 0.20/0.51  % (17087)Time elapsed: 0.080 s
% 0.20/0.51  % (17087)------------------------------
% 0.20/0.51  % (17087)------------------------------
% 0.20/0.51  % (17077)Success in time 0.152 s
%------------------------------------------------------------------------------
