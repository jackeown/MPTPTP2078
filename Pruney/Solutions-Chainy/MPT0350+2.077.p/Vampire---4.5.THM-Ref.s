%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:01 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 134 expanded)
%              Number of leaves         :   28 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :  191 ( 266 expanded)
%              Number of equality atoms :   55 (  76 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f240,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f70,f77,f84,f90,f102,f108,f115,f137,f177,f204,f237,f239])).

% (27421)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f239,plain,
    ( k3_subset_1(sK0,sK1) != k5_xboole_0(sK0,sK1)
    | k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) != k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK1)))
    | sK0 != k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK1)))
    | sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f237,plain,
    ( spl3_26
    | ~ spl3_2
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f227,f174,f56,f234])).

fof(f234,plain,
    ( spl3_26
  <=> k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f56,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f174,plain,
    ( spl3_18
  <=> m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f227,plain,
    ( k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK1)))
    | ~ spl3_2
    | ~ spl3_18 ),
    inference(resolution,[],[f222,f176])).

fof(f176,plain,
    ( m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f174])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,sK1,X0) = k3_tarski(k1_enumset1(sK1,sK1,X0)) )
    | ~ spl3_2 ),
    inference(resolution,[],[f47,f58])).

fof(f58,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f43,f44])).

% (27435)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f204,plain,
    ( spl3_22
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f194,f96,f201])).

fof(f201,plain,
    ( spl3_22
  <=> sK0 = k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f96,plain,
    ( spl3_8
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f194,plain,
    ( sK0 = k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK1)))
    | ~ spl3_8 ),
    inference(superposition,[],[f45,f98])).

fof(f98,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f45,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f31,f44,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f177,plain,
    ( spl3_18
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f161,f112,f105,f174])).

fof(f105,plain,
    ( spl3_9
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f112,plain,
    ( spl3_10
  <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f161,plain,
    ( m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f107,f114])).

fof(f114,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f112])).

fof(f107,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f137,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl3_3 ),
    inference(resolution,[],[f65,f25])).

fof(f25,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f65,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_3
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f115,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f110,f96,f56,f112])).

fof(f110,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f109,f98])).

fof(f109,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_2 ),
    inference(resolution,[],[f46,f58])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f108,plain,
    ( spl3_9
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f103,f56,f105])).

fof(f103,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f37,f58])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f102,plain,
    ( spl3_8
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f94,f81,f96])).

fof(f81,plain,
    ( spl3_6
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f94,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_6 ),
    inference(superposition,[],[f27,f83])).

fof(f83,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f90,plain,
    ( ~ spl3_7
    | spl3_1 ),
    inference(avatar_split_clause,[],[f85,f51,f87])).

fof(f87,plain,
    ( spl3_7
  <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f51,plain,
    ( spl3_1
  <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f85,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl3_1 ),
    inference(forward_demodulation,[],[f53,f26])).

% (27443)Refutation not found, incomplete strategy% (27443)------------------------------
% (27443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27440)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (27443)Termination reason: Refutation not found, incomplete strategy

% (27443)Memory used [KB]: 10618
% (27443)Time elapsed: 0.082 s
% (27443)------------------------------
% (27443)------------------------------
% (27423)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (27450)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (27427)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (27444)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (27432)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (27446)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (27424)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f26,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f53,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f84,plain,
    ( spl3_6
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f78,f74,f81])).

fof(f74,plain,
    ( spl3_5
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f78,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f76,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f76,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f77,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f71,f67,f74])).

fof(f67,plain,
    ( spl3_4
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f71,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f69,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f69,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f70,plain,
    ( spl3_3
    | spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f61,f56,f67,f63])).

fof(f61,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f35,f58])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f59,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f56])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f54,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f24,f51])).

fof(f24,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (27434)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.50  % (27425)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.50  % (27437)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.50  % (27426)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.50  % (27429)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.51  % (27437)Refutation found. Thanks to Tanya!
% 0.19/0.51  % SZS status Theorem for theBenchmark
% 0.19/0.51  % (27422)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.51  % (27442)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.51  % (27448)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.51  % (27443)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.51  % (27445)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  fof(f240,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(avatar_sat_refutation,[],[f54,f59,f70,f77,f84,f90,f102,f108,f115,f137,f177,f204,f237,f239])).
% 0.19/0.51  % (27421)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.51  fof(f239,plain,(
% 0.19/0.51    k3_subset_1(sK0,sK1) != k5_xboole_0(sK0,sK1) | k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) != k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK1))) | sK0 != k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK1))) | sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.19/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.51  fof(f237,plain,(
% 0.19/0.51    spl3_26 | ~spl3_2 | ~spl3_18),
% 0.19/0.51    inference(avatar_split_clause,[],[f227,f174,f56,f234])).
% 0.19/0.51  fof(f234,plain,(
% 0.19/0.51    spl3_26 <=> k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK1)))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.19/0.51  fof(f56,plain,(
% 0.19/0.51    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.51  fof(f174,plain,(
% 0.19/0.51    spl3_18 <=> m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.19/0.51  fof(f227,plain,(
% 0.19/0.51    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK1))) | (~spl3_2 | ~spl3_18)),
% 0.19/0.51    inference(resolution,[],[f222,f176])).
% 0.19/0.51  fof(f176,plain,(
% 0.19/0.51    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_18),
% 0.19/0.51    inference(avatar_component_clause,[],[f174])).
% 0.19/0.51  fof(f222,plain,(
% 0.19/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,sK1,X0) = k3_tarski(k1_enumset1(sK1,sK1,X0))) ) | ~spl3_2),
% 0.19/0.51    inference(resolution,[],[f47,f58])).
% 0.19/0.51  fof(f58,plain,(
% 0.19/0.51    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.19/0.51    inference(avatar_component_clause,[],[f56])).
% 0.19/0.51  fof(f47,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))) )),
% 0.19/0.51    inference(definition_unfolding,[],[f43,f44])).
% 0.19/0.51  % (27435)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.51  fof(f44,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.19/0.51    inference(definition_unfolding,[],[f28,f29])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f5])).
% 0.19/0.51  fof(f5,axiom,(
% 0.19/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f7])).
% 0.19/0.51  fof(f7,axiom,(
% 0.19/0.51    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.19/0.51  fof(f43,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f22])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.51    inference(flattening,[],[f21])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.19/0.51    inference(ennf_transformation,[],[f13])).
% 0.19/0.51  fof(f13,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.19/0.51  fof(f204,plain,(
% 0.19/0.51    spl3_22 | ~spl3_8),
% 0.19/0.51    inference(avatar_split_clause,[],[f194,f96,f201])).
% 0.19/0.51  fof(f201,plain,(
% 0.19/0.51    spl3_22 <=> sK0 = k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK1)))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.19/0.51  fof(f96,plain,(
% 0.19/0.51    spl3_8 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.19/0.51  fof(f194,plain,(
% 0.19/0.51    sK0 = k3_tarski(k1_enumset1(sK1,sK1,k5_xboole_0(sK0,sK1))) | ~spl3_8),
% 0.19/0.51    inference(superposition,[],[f45,f98])).
% 0.19/0.51  fof(f98,plain,(
% 0.19/0.51    sK1 = k3_xboole_0(sK0,sK1) | ~spl3_8),
% 0.19/0.51    inference(avatar_component_clause,[],[f96])).
% 0.19/0.51  fof(f45,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0) )),
% 0.19/0.51    inference(definition_unfolding,[],[f31,f44,f30])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.19/0.51  fof(f31,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.19/0.51    inference(cnf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.19/0.51  fof(f177,plain,(
% 0.19/0.51    spl3_18 | ~spl3_9 | ~spl3_10),
% 0.19/0.51    inference(avatar_split_clause,[],[f161,f112,f105,f174])).
% 0.19/0.51  fof(f105,plain,(
% 0.19/0.51    spl3_9 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.19/0.51  fof(f112,plain,(
% 0.19/0.51    spl3_10 <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.51  fof(f161,plain,(
% 0.19/0.51    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | (~spl3_9 | ~spl3_10)),
% 0.19/0.51    inference(backward_demodulation,[],[f107,f114])).
% 0.19/0.51  fof(f114,plain,(
% 0.19/0.51    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) | ~spl3_10),
% 0.19/0.51    inference(avatar_component_clause,[],[f112])).
% 0.19/0.51  fof(f107,plain,(
% 0.19/0.51    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_9),
% 0.19/0.51    inference(avatar_component_clause,[],[f105])).
% 0.19/0.51  fof(f137,plain,(
% 0.19/0.51    ~spl3_3),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f135])).
% 0.19/0.51  fof(f135,plain,(
% 0.19/0.51    $false | ~spl3_3),
% 0.19/0.51    inference(resolution,[],[f65,f25])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f12])).
% 0.19/0.51  fof(f12,axiom,(
% 0.19/0.51    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.19/0.51  fof(f65,plain,(
% 0.19/0.51    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.19/0.51    inference(avatar_component_clause,[],[f63])).
% 0.19/0.51  fof(f63,plain,(
% 0.19/0.51    spl3_3 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.51  fof(f115,plain,(
% 0.19/0.51    spl3_10 | ~spl3_2 | ~spl3_8),
% 0.19/0.51    inference(avatar_split_clause,[],[f110,f96,f56,f112])).
% 0.19/0.51  fof(f110,plain,(
% 0.19/0.51    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) | (~spl3_2 | ~spl3_8)),
% 0.19/0.51    inference(forward_demodulation,[],[f109,f98])).
% 0.19/0.51  fof(f109,plain,(
% 0.19/0.51    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_2),
% 0.19/0.51    inference(resolution,[],[f46,f58])).
% 0.19/0.51  fof(f46,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f38,f30])).
% 0.19/0.51  fof(f38,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f10])).
% 0.19/0.51  fof(f10,axiom,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.19/0.51  fof(f108,plain,(
% 0.19/0.51    spl3_9 | ~spl3_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f103,f56,f105])).
% 0.19/0.51  fof(f103,plain,(
% 0.19/0.51    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.19/0.51    inference(resolution,[],[f37,f58])).
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f19])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f11])).
% 0.19/0.51  fof(f11,axiom,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.19/0.51  fof(f102,plain,(
% 0.19/0.51    spl3_8 | ~spl3_6),
% 0.19/0.51    inference(avatar_split_clause,[],[f94,f81,f96])).
% 0.19/0.51  fof(f81,plain,(
% 0.19/0.51    spl3_6 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.51  fof(f94,plain,(
% 0.19/0.51    sK1 = k3_xboole_0(sK0,sK1) | ~spl3_6),
% 0.19/0.51    inference(superposition,[],[f27,f83])).
% 0.19/0.51  fof(f83,plain,(
% 0.19/0.51    sK1 = k3_xboole_0(sK1,sK0) | ~spl3_6),
% 0.19/0.51    inference(avatar_component_clause,[],[f81])).
% 0.19/0.51  fof(f27,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.51  fof(f90,plain,(
% 0.19/0.51    ~spl3_7 | spl3_1),
% 0.19/0.51    inference(avatar_split_clause,[],[f85,f51,f87])).
% 0.19/0.51  fof(f87,plain,(
% 0.19/0.51    spl3_7 <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.51  fof(f51,plain,(
% 0.19/0.51    spl3_1 <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.51  fof(f85,plain,(
% 0.19/0.51    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl3_1),
% 0.19/0.51    inference(forward_demodulation,[],[f53,f26])).
% 0.19/0.52  % (27443)Refutation not found, incomplete strategy% (27443)------------------------------
% 0.19/0.52  % (27443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (27440)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.52  % (27443)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (27443)Memory used [KB]: 10618
% 0.19/0.52  % (27443)Time elapsed: 0.082 s
% 0.19/0.52  % (27443)------------------------------
% 0.19/0.52  % (27443)------------------------------
% 0.19/0.52  % (27423)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.52  % (27450)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.52  % (27427)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.52  % (27444)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.52  % (27432)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.52  % (27446)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.52  % (27424)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.53  fof(f26,plain,(
% 1.36/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.36/0.53    inference(cnf_transformation,[],[f9])).
% 1.36/0.53  fof(f9,axiom,(
% 1.36/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.36/0.53  fof(f53,plain,(
% 1.36/0.53    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl3_1),
% 1.36/0.53    inference(avatar_component_clause,[],[f51])).
% 1.36/0.53  fof(f84,plain,(
% 1.36/0.53    spl3_6 | ~spl3_5),
% 1.36/0.53    inference(avatar_split_clause,[],[f78,f74,f81])).
% 1.36/0.53  fof(f74,plain,(
% 1.36/0.53    spl3_5 <=> r1_tarski(sK1,sK0)),
% 1.36/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.36/0.53  fof(f78,plain,(
% 1.36/0.53    sK1 = k3_xboole_0(sK1,sK0) | ~spl3_5),
% 1.36/0.53    inference(resolution,[],[f76,f36])).
% 1.36/0.53  fof(f36,plain,(
% 1.36/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.36/0.53    inference(cnf_transformation,[],[f18])).
% 1.36/0.53  fof(f18,plain,(
% 1.36/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.36/0.53    inference(ennf_transformation,[],[f3])).
% 1.36/0.53  fof(f3,axiom,(
% 1.36/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.36/0.53  fof(f76,plain,(
% 1.36/0.53    r1_tarski(sK1,sK0) | ~spl3_5),
% 1.36/0.53    inference(avatar_component_clause,[],[f74])).
% 1.36/0.53  fof(f77,plain,(
% 1.36/0.53    spl3_5 | ~spl3_4),
% 1.36/0.53    inference(avatar_split_clause,[],[f71,f67,f74])).
% 1.36/0.53  fof(f67,plain,(
% 1.36/0.53    spl3_4 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.36/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.36/0.53  fof(f71,plain,(
% 1.36/0.53    r1_tarski(sK1,sK0) | ~spl3_4),
% 1.36/0.53    inference(resolution,[],[f69,f48])).
% 1.36/0.53  fof(f48,plain,(
% 1.36/0.53    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.36/0.53    inference(equality_resolution,[],[f40])).
% 1.36/0.53  fof(f40,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.36/0.53    inference(cnf_transformation,[],[f6])).
% 1.36/0.53  fof(f6,axiom,(
% 1.36/0.53    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.36/0.53  fof(f69,plain,(
% 1.36/0.53    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_4),
% 1.36/0.53    inference(avatar_component_clause,[],[f67])).
% 1.36/0.53  fof(f70,plain,(
% 1.36/0.53    spl3_3 | spl3_4 | ~spl3_2),
% 1.36/0.53    inference(avatar_split_clause,[],[f61,f56,f67,f63])).
% 1.36/0.53  fof(f61,plain,(
% 1.36/0.53    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_2),
% 1.36/0.53    inference(resolution,[],[f35,f58])).
% 1.36/0.53  fof(f35,plain,(
% 1.36/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f17])).
% 1.36/0.53  fof(f17,plain,(
% 1.36/0.53    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.36/0.53    inference(ennf_transformation,[],[f8])).
% 1.36/0.53  fof(f8,axiom,(
% 1.36/0.53    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.36/0.53  fof(f59,plain,(
% 1.36/0.53    spl3_2),
% 1.36/0.53    inference(avatar_split_clause,[],[f23,f56])).
% 1.36/0.53  fof(f23,plain,(
% 1.36/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.36/0.53    inference(cnf_transformation,[],[f16])).
% 1.36/0.53  fof(f16,plain,(
% 1.36/0.53    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.36/0.53    inference(ennf_transformation,[],[f15])).
% 1.36/0.53  fof(f15,negated_conjecture,(
% 1.36/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.36/0.53    inference(negated_conjecture,[],[f14])).
% 1.36/0.53  fof(f14,conjecture,(
% 1.36/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 1.36/0.53  fof(f54,plain,(
% 1.36/0.53    ~spl3_1),
% 1.36/0.53    inference(avatar_split_clause,[],[f24,f51])).
% 1.36/0.53  fof(f24,plain,(
% 1.36/0.53    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.36/0.53    inference(cnf_transformation,[],[f16])).
% 1.36/0.53  % SZS output end Proof for theBenchmark
% 1.36/0.53  % (27437)------------------------------
% 1.36/0.53  % (27437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  % (27437)Termination reason: Refutation
% 1.36/0.53  
% 1.36/0.53  % (27437)Memory used [KB]: 10874
% 1.36/0.53  % (27437)Time elapsed: 0.116 s
% 1.36/0.53  % (27437)------------------------------
% 1.36/0.53  % (27437)------------------------------
% 1.36/0.53  % (27420)Success in time 0.178 s
%------------------------------------------------------------------------------
