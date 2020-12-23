%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:43 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 277 expanded)
%              Number of leaves         :   27 (  98 expanded)
%              Depth                    :   14
%              Number of atoms          :  183 ( 403 expanded)
%              Number of equality atoms :   65 ( 215 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f511,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f88,f93,f143,f164,f181,f278,f480])).

fof(f480,plain,
    ( spl4_14
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f479,f178,f140,f90,f274])).

fof(f274,plain,
    ( spl4_14
  <=> sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f90,plain,
    ( spl4_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f140,plain,
    ( spl4_6
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

% (20068)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (20057)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (20061)Refutation not found, incomplete strategy% (20061)------------------------------
% (20061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20052)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (20065)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (20064)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (20051)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (20060)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (20056)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (20063)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f178,plain,
    ( spl4_10
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f479,plain,
    ( sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f478,f68])).

fof(f68,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f35,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f478,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f463,f244])).

fof(f244,plain,
    ( ! [X9] : k1_xboole_0 = k5_xboole_0(X9,X9)
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f243,f142])).

fof(f142,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f140])).

fof(f243,plain,
    ( ! [X9] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(X9,X9)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f242,f111])).

fof(f111,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl4_3 ),
    inference(resolution,[],[f108,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f108,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_3 ),
    inference(resolution,[],[f107,f92])).

fof(f92,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f55,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f242,plain,(
    ! [X9] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X9)) = k5_xboole_0(X9,X9) ),
    inference(forward_demodulation,[],[f239,f105])).

fof(f105,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f49,f77])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f239,plain,(
    ! [X9] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X9)) = k5_xboole_0(X9,k3_xboole_0(X9,X9)) ),
    inference(superposition,[],[f233,f186])).

fof(f186,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f69,f68])).

fof(f69,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f39,f65,f65])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f233,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(X1,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) ),
    inference(forward_demodulation,[],[f70,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f70,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f43,f42,f42,f65])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f463,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
    | ~ spl4_10 ),
    inference(superposition,[],[f72,f180])).

fof(f180,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f178])).

fof(f72,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f45,f65,f65,f42])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f278,plain,
    ( ~ spl4_14
    | spl4_1 ),
    inference(avatar_split_clause,[],[f253,f80,f274])).

fof(f80,plain,
    ( spl4_1
  <=> sK1 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f253,plain,
    ( sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl4_1 ),
    inference(superposition,[],[f82,f69])).

fof(f82,plain,
    ( sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f181,plain,
    ( spl4_10
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f167,f161,f178])).

fof(f161,plain,
    ( spl4_7
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f167,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_7 ),
    inference(resolution,[],[f163,f49])).

fof(f163,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f161])).

fof(f164,plain,
    ( spl4_7
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f156,f85,f161])).

fof(f85,plain,
    ( spl4_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f156,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f76,f87])).

fof(f87,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f59,f66])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f64])).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f143,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f138,f90,f140])).

fof(f138,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f136,f111])).

fof(f136,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))
    | ~ spl4_3 ),
    inference(resolution,[],[f73,f101])).

fof(f101,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl4_3 ),
    inference(resolution,[],[f100,f92])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f47,f37])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
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

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f58,f42])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f93,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f34,f90])).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f88,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f32,f85])).

fof(f32,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f83,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f67,f80])).

fof(f67,plain,(
    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f33,f65,f66])).

fof(f33,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.10  % Command    : run_vampire %s %d
% 0.10/0.31  % Computer   : n019.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 13:51:07 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.18/0.47  % (20047)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.18/0.48  % (20039)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.18/0.49  % (20043)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.18/0.49  % (20047)Refutation not found, incomplete strategy% (20047)------------------------------
% 0.18/0.49  % (20047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (20047)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.49  
% 0.18/0.49  % (20047)Memory used [KB]: 10618
% 0.18/0.49  % (20047)Time elapsed: 0.101 s
% 0.18/0.49  % (20047)------------------------------
% 0.18/0.49  % (20047)------------------------------
% 0.18/0.49  % (20054)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.18/0.49  % (20055)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.18/0.49  % (20045)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.18/0.50  % (20046)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.18/0.50  % (20062)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.18/0.50  % (20059)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.18/0.50  % (20041)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.18/0.51  % (20041)Refutation not found, incomplete strategy% (20041)------------------------------
% 0.18/0.51  % (20041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (20041)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.51  
% 0.18/0.51  % (20041)Memory used [KB]: 10746
% 0.18/0.51  % (20041)Time elapsed: 0.124 s
% 0.18/0.51  % (20041)------------------------------
% 0.18/0.51  % (20041)------------------------------
% 0.18/0.51  % (20044)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.18/0.51  % (20040)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.18/0.51  % (20053)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.18/0.51  % (20049)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.18/0.51  % (20049)Refutation not found, incomplete strategy% (20049)------------------------------
% 0.18/0.51  % (20049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (20049)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.51  
% 0.18/0.51  % (20049)Memory used [KB]: 10618
% 0.18/0.51  % (20049)Time elapsed: 0.125 s
% 0.18/0.51  % (20049)------------------------------
% 0.18/0.51  % (20049)------------------------------
% 0.18/0.51  % (20048)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.18/0.51  % (20067)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.18/0.51  % (20055)Refutation found. Thanks to Tanya!
% 0.18/0.51  % SZS status Theorem for theBenchmark
% 0.18/0.51  % (20061)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.18/0.51  % SZS output start Proof for theBenchmark
% 0.18/0.51  fof(f511,plain,(
% 0.18/0.51    $false),
% 0.18/0.51    inference(avatar_sat_refutation,[],[f83,f88,f93,f143,f164,f181,f278,f480])).
% 0.18/0.51  fof(f480,plain,(
% 0.18/0.51    spl4_14 | ~spl4_3 | ~spl4_6 | ~spl4_10),
% 0.18/0.51    inference(avatar_split_clause,[],[f479,f178,f140,f90,f274])).
% 0.18/0.51  fof(f274,plain,(
% 0.18/0.51    spl4_14 <=> sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.18/0.51  fof(f90,plain,(
% 0.18/0.51    spl4_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.18/0.51  fof(f140,plain,(
% 0.18/0.51    spl4_6 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.18/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.18/0.51  % (20068)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.18/0.51  % (20057)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.18/0.52  % (20061)Refutation not found, incomplete strategy% (20061)------------------------------
% 0.18/0.52  % (20061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.52  % (20052)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.18/0.52  % (20065)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.18/0.52  % (20064)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.18/0.52  % (20051)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.52  % (20060)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.18/0.52  % (20056)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.18/0.52  % (20063)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.18/0.53  fof(f178,plain,(
% 0.18/0.53    spl4_10 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 0.18/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.18/0.53  fof(f479,plain,(
% 0.18/0.53    sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | (~spl4_3 | ~spl4_6 | ~spl4_10)),
% 0.18/0.53    inference(forward_demodulation,[],[f478,f68])).
% 0.18/0.53  fof(f68,plain,(
% 0.18/0.53    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 0.18/0.53    inference(definition_unfolding,[],[f35,f65])).
% 0.18/0.53  fof(f65,plain,(
% 0.18/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.18/0.53    inference(definition_unfolding,[],[f40,f64])).
% 0.18/0.53  fof(f64,plain,(
% 0.18/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.18/0.53    inference(definition_unfolding,[],[f41,f63])).
% 0.18/0.53  fof(f63,plain,(
% 0.18/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.18/0.53    inference(definition_unfolding,[],[f61,f62])).
% 0.18/0.53  fof(f62,plain,(
% 0.18/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f19])).
% 0.18/0.53  fof(f19,axiom,(
% 0.18/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.18/0.53  fof(f61,plain,(
% 0.18/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f18])).
% 0.18/0.53  fof(f18,axiom,(
% 0.18/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.18/0.53  fof(f41,plain,(
% 0.18/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f17])).
% 0.18/0.53  fof(f17,axiom,(
% 0.18/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.18/0.53  fof(f40,plain,(
% 0.18/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.18/0.53    inference(cnf_transformation,[],[f21])).
% 0.18/0.53  fof(f21,axiom,(
% 0.18/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.18/0.53  fof(f35,plain,(
% 0.18/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.18/0.53    inference(cnf_transformation,[],[f10])).
% 0.18/0.53  fof(f10,axiom,(
% 0.18/0.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.18/0.53  fof(f478,plain,(
% 0.18/0.53    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0)) | (~spl4_3 | ~spl4_6 | ~spl4_10)),
% 0.18/0.53    inference(forward_demodulation,[],[f463,f244])).
% 0.18/0.53  fof(f244,plain,(
% 0.18/0.53    ( ! [X9] : (k1_xboole_0 = k5_xboole_0(X9,X9)) ) | (~spl4_3 | ~spl4_6)),
% 0.18/0.53    inference(forward_demodulation,[],[f243,f142])).
% 0.18/0.53  fof(f142,plain,(
% 0.18/0.53    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_6),
% 0.18/0.53    inference(avatar_component_clause,[],[f140])).
% 0.18/0.53  fof(f243,plain,(
% 0.18/0.53    ( ! [X9] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(X9,X9)) ) | ~spl4_3),
% 0.18/0.53    inference(forward_demodulation,[],[f242,f111])).
% 0.18/0.53  fof(f111,plain,(
% 0.18/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl4_3),
% 0.18/0.53    inference(resolution,[],[f108,f49])).
% 0.18/0.53  fof(f49,plain,(
% 0.18/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.18/0.53    inference(cnf_transformation,[],[f29])).
% 0.18/0.53  fof(f29,plain,(
% 0.18/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.18/0.53    inference(ennf_transformation,[],[f11])).
% 0.18/0.53  fof(f11,axiom,(
% 0.18/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.18/0.53  fof(f108,plain,(
% 0.18/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_3),
% 0.18/0.53    inference(resolution,[],[f107,f92])).
% 0.18/0.53  fof(f92,plain,(
% 0.18/0.53    v1_xboole_0(k1_xboole_0) | ~spl4_3),
% 0.18/0.53    inference(avatar_component_clause,[],[f90])).
% 0.18/0.53  fof(f107,plain,(
% 0.18/0.53    ( ! [X0,X1] : (~v1_xboole_0(X0) | r1_tarski(X0,X1)) )),
% 0.18/0.53    inference(resolution,[],[f55,f37])).
% 0.18/0.53  fof(f37,plain,(
% 0.18/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f27])).
% 0.18/0.53  fof(f27,plain,(
% 0.18/0.53    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.18/0.53    inference(ennf_transformation,[],[f25])).
% 0.18/0.53  fof(f25,plain,(
% 0.18/0.53    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.18/0.53    inference(unused_predicate_definition_removal,[],[f3])).
% 0.18/0.53  fof(f3,axiom,(
% 0.18/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.18/0.53  fof(f55,plain,(
% 0.18/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f31])).
% 0.18/0.53  fof(f31,plain,(
% 0.18/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.18/0.53    inference(ennf_transformation,[],[f4])).
% 0.18/0.53  fof(f4,axiom,(
% 0.18/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.18/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.18/0.53  fof(f242,plain,(
% 0.18/0.53    ( ! [X9] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X9)) = k5_xboole_0(X9,X9)) )),
% 0.18/0.53    inference(forward_demodulation,[],[f239,f105])).
% 1.53/0.53  fof(f105,plain,(
% 1.53/0.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.53/0.53    inference(resolution,[],[f49,f77])).
% 1.53/0.53  fof(f77,plain,(
% 1.53/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.53/0.53    inference(equality_resolution,[],[f52])).
% 1.53/0.53  fof(f52,plain,(
% 1.53/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.53/0.53    inference(cnf_transformation,[],[f8])).
% 1.53/0.53  fof(f8,axiom,(
% 1.53/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.53/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.53/0.53  fof(f239,plain,(
% 1.53/0.53    ( ! [X9] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X9)) = k5_xboole_0(X9,k3_xboole_0(X9,X9))) )),
% 1.53/0.53    inference(superposition,[],[f233,f186])).
% 1.53/0.53  fof(f186,plain,(
% 1.53/0.53    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.53/0.53    inference(superposition,[],[f69,f68])).
% 1.53/0.53  fof(f69,plain,(
% 1.53/0.53    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 1.53/0.53    inference(definition_unfolding,[],[f39,f65,f65])).
% 1.53/0.53  fof(f39,plain,(
% 1.53/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.53/0.53    inference(cnf_transformation,[],[f1])).
% 1.53/0.53  fof(f1,axiom,(
% 1.53/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.53/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.53/0.53  fof(f233,plain,(
% 1.53/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(X1,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))))) )),
% 1.53/0.53    inference(forward_demodulation,[],[f70,f38])).
% 1.53/0.53  fof(f38,plain,(
% 1.53/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.53/0.53    inference(cnf_transformation,[],[f2])).
% 1.53/0.53  fof(f2,axiom,(
% 1.53/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.53/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.53/0.53  fof(f70,plain,(
% 1.53/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 1.53/0.53    inference(definition_unfolding,[],[f43,f42,f42,f65])).
% 1.53/0.53  fof(f42,plain,(
% 1.53/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.53/0.53    inference(cnf_transformation,[],[f9])).
% 1.53/0.53  fof(f9,axiom,(
% 1.53/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.53/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.53/0.53  fof(f43,plain,(
% 1.53/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.53/0.53    inference(cnf_transformation,[],[f13])).
% 1.53/0.53  fof(f13,axiom,(
% 1.53/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.53/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.53/0.53  fof(f463,plain,(
% 1.53/0.53    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | ~spl4_10),
% 1.53/0.53    inference(superposition,[],[f72,f180])).
% 1.53/0.53  fof(f180,plain,(
% 1.53/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl4_10),
% 1.53/0.53    inference(avatar_component_clause,[],[f178])).
% 1.53/0.53  fof(f72,plain,(
% 1.53/0.53    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.53/0.53    inference(definition_unfolding,[],[f45,f65,f65,f42])).
% 1.53/0.53  fof(f45,plain,(
% 1.53/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.53/0.53    inference(cnf_transformation,[],[f12])).
% 1.53/0.53  fof(f12,axiom,(
% 1.53/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.53/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.53/0.53  fof(f278,plain,(
% 1.53/0.53    ~spl4_14 | spl4_1),
% 1.53/0.53    inference(avatar_split_clause,[],[f253,f80,f274])).
% 1.53/0.53  fof(f80,plain,(
% 1.53/0.53    spl4_1 <=> sK1 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.53/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.53/0.53  fof(f253,plain,(
% 1.53/0.53    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl4_1),
% 1.53/0.53    inference(superposition,[],[f82,f69])).
% 1.53/0.53  fof(f82,plain,(
% 1.53/0.53    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) | spl4_1),
% 1.53/0.53    inference(avatar_component_clause,[],[f80])).
% 1.53/0.53  fof(f181,plain,(
% 1.53/0.53    spl4_10 | ~spl4_7),
% 1.53/0.53    inference(avatar_split_clause,[],[f167,f161,f178])).
% 1.53/0.53  fof(f161,plain,(
% 1.53/0.53    spl4_7 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.53/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.53/0.53  fof(f167,plain,(
% 1.53/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl4_7),
% 1.53/0.53    inference(resolution,[],[f163,f49])).
% 1.53/0.53  fof(f163,plain,(
% 1.53/0.53    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl4_7),
% 1.53/0.53    inference(avatar_component_clause,[],[f161])).
% 1.53/0.53  fof(f164,plain,(
% 1.53/0.53    spl4_7 | ~spl4_2),
% 1.53/0.53    inference(avatar_split_clause,[],[f156,f85,f161])).
% 1.53/0.53  fof(f85,plain,(
% 1.53/0.53    spl4_2 <=> r2_hidden(sK0,sK1)),
% 1.53/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.53/0.53  fof(f156,plain,(
% 1.53/0.53    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl4_2),
% 1.53/0.53    inference(resolution,[],[f76,f87])).
% 1.53/0.53  fof(f87,plain,(
% 1.53/0.53    r2_hidden(sK0,sK1) | ~spl4_2),
% 1.53/0.53    inference(avatar_component_clause,[],[f85])).
% 1.53/0.53  fof(f76,plain,(
% 1.53/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 1.53/0.53    inference(definition_unfolding,[],[f59,f66])).
% 1.53/0.53  fof(f66,plain,(
% 1.53/0.53    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.53/0.53    inference(definition_unfolding,[],[f36,f64])).
% 1.53/0.53  fof(f36,plain,(
% 1.53/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.53/0.53    inference(cnf_transformation,[],[f16])).
% 1.53/0.53  fof(f16,axiom,(
% 1.53/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.53/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.53/0.53  fof(f59,plain,(
% 1.53/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.53/0.53    inference(cnf_transformation,[],[f20])).
% 1.53/0.53  fof(f20,axiom,(
% 1.53/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.53/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.53/0.53  fof(f143,plain,(
% 1.53/0.53    spl4_6 | ~spl4_3),
% 1.53/0.53    inference(avatar_split_clause,[],[f138,f90,f140])).
% 1.53/0.53  fof(f138,plain,(
% 1.53/0.53    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_3),
% 1.53/0.53    inference(forward_demodulation,[],[f136,f111])).
% 1.53/0.53  fof(f136,plain,(
% 1.53/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) ) | ~spl4_3),
% 1.53/0.53    inference(resolution,[],[f73,f101])).
% 1.53/0.53  fof(f101,plain,(
% 1.53/0.53    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | ~spl4_3),
% 1.53/0.53    inference(resolution,[],[f100,f92])).
% 1.53/0.53  fof(f100,plain,(
% 1.53/0.53    ( ! [X0,X1] : (~v1_xboole_0(X0) | r1_xboole_0(X0,X1)) )),
% 1.53/0.53    inference(resolution,[],[f47,f37])).
% 1.53/0.53  fof(f47,plain,(
% 1.53/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.53/0.53    inference(cnf_transformation,[],[f28])).
% 1.53/0.53  fof(f28,plain,(
% 1.53/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.53/0.53    inference(ennf_transformation,[],[f24])).
% 1.53/0.53  fof(f24,plain,(
% 1.53/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.53/0.53    inference(rectify,[],[f7])).
% 1.53/0.53  fof(f7,axiom,(
% 1.53/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.53/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.53/0.53  fof(f73,plain,(
% 1.53/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.53/0.53    inference(definition_unfolding,[],[f58,f42])).
% 1.53/0.53  fof(f58,plain,(
% 1.53/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.53/0.53    inference(cnf_transformation,[],[f14])).
% 1.53/0.53  fof(f14,axiom,(
% 1.53/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.53/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.53/0.53  fof(f93,plain,(
% 1.53/0.53    spl4_3),
% 1.53/0.53    inference(avatar_split_clause,[],[f34,f90])).
% 1.53/0.53  fof(f34,plain,(
% 1.53/0.53    v1_xboole_0(k1_xboole_0)),
% 1.53/0.53    inference(cnf_transformation,[],[f5])).
% 1.53/0.53  fof(f5,axiom,(
% 1.53/0.53    v1_xboole_0(k1_xboole_0)),
% 1.53/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.53/0.53  fof(f88,plain,(
% 1.53/0.53    spl4_2),
% 1.53/0.53    inference(avatar_split_clause,[],[f32,f85])).
% 1.53/0.53  fof(f32,plain,(
% 1.53/0.53    r2_hidden(sK0,sK1)),
% 1.53/0.53    inference(cnf_transformation,[],[f26])).
% 1.53/0.53  fof(f26,plain,(
% 1.53/0.53    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.53/0.53    inference(ennf_transformation,[],[f23])).
% 1.53/0.53  fof(f23,negated_conjecture,(
% 1.53/0.53    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.53/0.53    inference(negated_conjecture,[],[f22])).
% 1.53/0.53  fof(f22,conjecture,(
% 1.53/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.53/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.53/0.53  fof(f83,plain,(
% 1.53/0.53    ~spl4_1),
% 1.53/0.53    inference(avatar_split_clause,[],[f67,f80])).
% 1.53/0.53  fof(f67,plain,(
% 1.53/0.53    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.53/0.53    inference(definition_unfolding,[],[f33,f65,f66])).
% 1.53/0.53  fof(f33,plain,(
% 1.53/0.53    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.53/0.53    inference(cnf_transformation,[],[f26])).
% 1.53/0.53  % SZS output end Proof for theBenchmark
% 1.53/0.53  % (20055)------------------------------
% 1.53/0.53  % (20055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.53  % (20055)Termination reason: Refutation
% 1.53/0.53  
% 1.53/0.53  % (20055)Memory used [KB]: 11001
% 1.53/0.53  % (20055)Time elapsed: 0.134 s
% 1.53/0.53  % (20055)------------------------------
% 1.53/0.53  % (20055)------------------------------
% 1.53/0.53  % (20038)Success in time 0.199 s
%------------------------------------------------------------------------------
