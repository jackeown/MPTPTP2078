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
% DateTime   : Thu Dec  3 12:50:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 211 expanded)
%              Number of leaves         :   26 (  87 expanded)
%              Depth                    :   10
%              Number of atoms          :  215 ( 418 expanded)
%              Number of equality atoms :   37 ( 117 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f406,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f76,f81,f86,f91,f204,f267,f315,f360,f364,f395,f400,f404])).

fof(f404,plain,
    ( spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f401,f122,f78])).

fof(f78,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f122,plain,
    ( spl3_9
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f401,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_9 ),
    inference(resolution,[],[f123,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f40,f28])).

fof(f28,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f123,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f400,plain,
    ( spl3_9
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f399,f392,f122])).

fof(f392,plain,
    ( spl3_35
  <=> r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

% (5593)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f399,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f398,f29])).

fof(f29,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f398,plain,
    ( r1_tarski(sK1,k3_tarski(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl3_35 ),
    inference(resolution,[],[f394,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f394,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f392])).

fof(f395,plain,
    ( spl3_35
    | ~ spl3_5
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f389,f201,f83,f392])).

% (5591)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (5589)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f83,plain,
    ( spl3_5
  <=> r2_hidden(sK1,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f201,plain,
    ( spl3_20
  <=> r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f389,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_5
    | ~ spl3_20 ),
    inference(resolution,[],[f378,f203])).

fof(f203,plain,
    ( r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f201])).

fof(f378,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relat_1(sK0),X1)
        | r2_hidden(sK1,X1) )
    | ~ spl3_5 ),
    inference(resolution,[],[f85,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f85,plain,
    ( r2_hidden(sK1,k2_relat_1(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f364,plain,
    ( spl3_2
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f361,f201,f88,f65,f70])).

fof(f70,plain,
    ( spl3_2
  <=> v3_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f65,plain,
    ( spl3_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f88,plain,
    ( spl3_6
  <=> k1_zfmisc_1(k1_xboole_0) = k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f361,plain,
    ( ~ v1_relat_1(sK0)
    | v3_relat_1(sK0)
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(resolution,[],[f203,f258])).

fof(f258,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(X0),k1_zfmisc_1(k1_xboole_0))
        | ~ v1_relat_1(X0)
        | v3_relat_1(X0) )
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f58,f90])).

fof(f90,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
      | v3_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f33,f54])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | v3_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_relat_1)).

fof(f360,plain,
    ( spl3_20
    | ~ spl3_28
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f358,f312,f262,f201])).

fof(f262,plain,
    ( spl3_28
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f312,plain,
    ( spl3_31
  <=> k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f358,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_31 ),
    inference(superposition,[],[f43,f314])).

fof(f314,plain,
    ( k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f312])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f315,plain,
    ( spl3_2
    | ~ spl3_1
    | spl3_31
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f307,f88,f74,f312,f65,f70])).

fof(f74,plain,
    ( spl3_3
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK0))
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f307,plain,
    ( k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | v3_relat_1(sK0)
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(resolution,[],[f280,f258])).

fof(f280,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(sK0),X0)
        | k1_xboole_0 = sK2(k2_relat_1(sK0),X0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f75,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f75,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK0))
        | k1_xboole_0 = X1 )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f267,plain,
    ( spl3_28
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f266,f88,f262])).

fof(f266,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f260,f29])).

fof(f260,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k3_tarski(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl3_6 ),
    inference(resolution,[],[f150,f31])).

fof(f31,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f150,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),X0)
        | r2_hidden(k1_xboole_0,X0) )
    | ~ spl3_6 ),
    inference(superposition,[],[f60,f90])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f46,f52])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f204,plain,
    ( spl3_20
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f199,f88,f70,f65,f201])).

fof(f199,plain,
    ( ~ v1_relat_1(sK0)
    | r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(resolution,[],[f196,f72])).

fof(f72,plain,
    ( v3_relat_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f196,plain,
    ( ! [X0] :
        ( ~ v3_relat_1(X0)
        | ~ v1_relat_1(X0)
        | r1_tarski(k2_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f57,f90])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
      | ~ v3_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f34,f54])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f91,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f55,f88])).

fof(f55,plain,(
    k1_zfmisc_1(k1_xboole_0) = k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f27,f54])).

fof(f27,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f86,plain,
    ( ~ spl3_2
    | spl3_5 ),
    inference(avatar_split_clause,[],[f23,f83,f70])).

fof(f23,plain,
    ( r2_hidden(sK1,k2_relat_1(sK0))
    | ~ v3_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ( v3_relat_1(X0)
      <~> ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) ) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v3_relat_1(X0)
        <=> ! [X1] :
              ( r2_hidden(X1,k2_relat_1(X0))
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k2_relat_1(X0))
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_relat_1)).

fof(f81,plain,
    ( ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f24,f78,f70])).

fof(f24,plain,
    ( k1_xboole_0 != sK1
    | ~ v3_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f76,plain,
    ( spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f25,f74,f70])).

fof(f25,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK0))
      | k1_xboole_0 = X1
      | v3_relat_1(sK0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f26,f65])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (5600)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (5608)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (5602)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.50  % (5608)Refutation not found, incomplete strategy% (5608)------------------------------
% 0.20/0.50  % (5608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5592)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (5608)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (5608)Memory used [KB]: 10618
% 0.20/0.51  % (5608)Time elapsed: 0.062 s
% 0.20/0.51  % (5608)------------------------------
% 0.20/0.51  % (5608)------------------------------
% 0.20/0.51  % (5590)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (5602)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (5611)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.52  % (5598)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (5587)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (5588)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f406,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f68,f76,f81,f86,f91,f204,f267,f315,f360,f364,f395,f400,f404])).
% 0.20/0.52  fof(f404,plain,(
% 0.20/0.52    spl3_4 | ~spl3_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f401,f122,f78])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    spl3_4 <=> k1_xboole_0 = sK1),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    spl3_9 <=> r1_tarski(sK1,k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.52  fof(f401,plain,(
% 0.20/0.52    k1_xboole_0 = sK1 | ~spl3_9),
% 0.20/0.52    inference(resolution,[],[f123,f97])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(resolution,[],[f40,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    r1_tarski(sK1,k1_xboole_0) | ~spl3_9),
% 0.20/0.52    inference(avatar_component_clause,[],[f122])).
% 0.20/0.52  fof(f400,plain,(
% 0.20/0.52    spl3_9 | ~spl3_35),
% 0.20/0.52    inference(avatar_split_clause,[],[f399,f392,f122])).
% 0.20/0.52  fof(f392,plain,(
% 0.20/0.52    spl3_35 <=> r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.52  % (5593)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  fof(f399,plain,(
% 0.20/0.52    r1_tarski(sK1,k1_xboole_0) | ~spl3_35),
% 0.20/0.52    inference(forward_demodulation,[],[f398,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,axiom,(
% 0.20/0.52    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.20/0.52  fof(f398,plain,(
% 0.20/0.52    r1_tarski(sK1,k3_tarski(k1_zfmisc_1(k1_xboole_0))) | ~spl3_35),
% 0.20/0.52    inference(resolution,[],[f394,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.20/0.52  fof(f394,plain,(
% 0.20/0.52    r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) | ~spl3_35),
% 0.20/0.52    inference(avatar_component_clause,[],[f392])).
% 0.20/0.52  fof(f395,plain,(
% 0.20/0.52    spl3_35 | ~spl3_5 | ~spl3_20),
% 0.20/0.52    inference(avatar_split_clause,[],[f389,f201,f83,f392])).
% 0.20/0.52  % (5591)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (5589)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    spl3_5 <=> r2_hidden(sK1,k2_relat_1(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.53  fof(f201,plain,(
% 0.20/0.53    spl3_20 <=> r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.53  fof(f389,plain,(
% 0.20/0.53    r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) | (~spl3_5 | ~spl3_20)),
% 0.20/0.53    inference(resolution,[],[f378,f203])).
% 0.20/0.53  fof(f203,plain,(
% 0.20/0.53    r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | ~spl3_20),
% 0.20/0.53    inference(avatar_component_clause,[],[f201])).
% 0.20/0.53  fof(f378,plain,(
% 0.20/0.53    ( ! [X1] : (~r1_tarski(k2_relat_1(sK0),X1) | r2_hidden(sK1,X1)) ) | ~spl3_5),
% 0.20/0.53    inference(resolution,[],[f85,f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    r2_hidden(sK1,k2_relat_1(sK0)) | ~spl3_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f83])).
% 0.20/0.53  fof(f364,plain,(
% 0.20/0.53    spl3_2 | ~spl3_1 | ~spl3_6 | ~spl3_20),
% 0.20/0.53    inference(avatar_split_clause,[],[f361,f201,f88,f65,f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    spl3_2 <=> v3_relat_1(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    spl3_1 <=> v1_relat_1(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    spl3_6 <=> k1_zfmisc_1(k1_xboole_0) = k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.53  fof(f361,plain,(
% 0.20/0.53    ~v1_relat_1(sK0) | v3_relat_1(sK0) | (~spl3_6 | ~spl3_20)),
% 0.20/0.53    inference(resolution,[],[f203,f258])).
% 0.20/0.53  fof(f258,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) | ~v1_relat_1(X0) | v3_relat_1(X0)) ) | ~spl3_6),
% 0.20/0.53    inference(forward_demodulation,[],[f58,f90])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    k1_zfmisc_1(k1_xboole_0) = k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl3_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f88])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | v3_relat_1(X0)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f33,f54])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f32,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f36,f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f44,f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f48,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | v3_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0] : ((v3_relat_1(X0) <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_relat_1)).
% 0.20/0.53  fof(f360,plain,(
% 0.20/0.53    spl3_20 | ~spl3_28 | ~spl3_31),
% 0.20/0.53    inference(avatar_split_clause,[],[f358,f312,f262,f201])).
% 0.20/0.53  fof(f262,plain,(
% 0.20/0.53    spl3_28 <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.53  fof(f312,plain,(
% 0.20/0.53    spl3_31 <=> k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.53  fof(f358,plain,(
% 0.20/0.53    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | ~spl3_31),
% 0.20/0.53    inference(superposition,[],[f43,f314])).
% 0.20/0.53  fof(f314,plain,(
% 0.20/0.53    k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | ~spl3_31),
% 0.20/0.53    inference(avatar_component_clause,[],[f312])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f315,plain,(
% 0.20/0.53    spl3_2 | ~spl3_1 | spl3_31 | ~spl3_3 | ~spl3_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f307,f88,f74,f312,f65,f70])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    spl3_3 <=> ! [X1] : (~r2_hidden(X1,k2_relat_1(sK0)) | k1_xboole_0 = X1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.53  fof(f307,plain,(
% 0.20/0.53    k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | ~v1_relat_1(sK0) | v3_relat_1(sK0) | (~spl3_3 | ~spl3_6)),
% 0.20/0.53    inference(resolution,[],[f280,f258])).
% 0.20/0.53  fof(f280,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k2_relat_1(sK0),X0) | k1_xboole_0 = sK2(k2_relat_1(sK0),X0)) ) | ~spl3_3),
% 0.20/0.53    inference(resolution,[],[f75,f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK0)) | k1_xboole_0 = X1) ) | ~spl3_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f74])).
% 0.20/0.53  fof(f267,plain,(
% 0.20/0.53    spl3_28 | ~spl3_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f266,f88,f262])).
% 0.20/0.53  fof(f266,plain,(
% 0.20/0.53    r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl3_6),
% 0.20/0.53    inference(forward_demodulation,[],[f260,f29])).
% 0.20/0.53  fof(f260,plain,(
% 0.20/0.53    r2_hidden(k1_xboole_0,k1_zfmisc_1(k3_tarski(k1_zfmisc_1(k1_xboole_0)))) | ~spl3_6),
% 0.20/0.53    inference(resolution,[],[f150,f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.20/0.53  fof(f150,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k1_zfmisc_1(k1_xboole_0),X0) | r2_hidden(k1_xboole_0,X0)) ) | ~spl3_6),
% 0.20/0.53    inference(superposition,[],[f60,f90])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f46,f52])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.20/0.53  fof(f204,plain,(
% 0.20/0.53    spl3_20 | ~spl3_1 | ~spl3_2 | ~spl3_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f199,f88,f70,f65,f201])).
% 0.20/0.53  fof(f199,plain,(
% 0.20/0.53    ~v1_relat_1(sK0) | r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | (~spl3_2 | ~spl3_6)),
% 0.20/0.53    inference(resolution,[],[f196,f72])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    v3_relat_1(sK0) | ~spl3_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f70])).
% 0.20/0.53  fof(f196,plain,(
% 0.20/0.53    ( ! [X0] : (~v3_relat_1(X0) | ~v1_relat_1(X0) | r1_tarski(k2_relat_1(X0),k1_zfmisc_1(k1_xboole_0))) ) | ~spl3_6),
% 0.20/0.53    inference(forward_demodulation,[],[f57,f90])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k2_relat_1(X0),k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | ~v3_relat_1(X0)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f34,f54])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | ~v3_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    spl3_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f55,f88])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    k1_zfmisc_1(k1_xboole_0) = k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.53    inference(definition_unfolding,[],[f27,f54])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,axiom,(
% 0.20/0.53    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    ~spl3_2 | spl3_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f23,f83,f70])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    r2_hidden(sK1,k2_relat_1(sK0)) | ~v3_relat_1(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ? [X0] : ((v3_relat_1(X0) <~> ! [X1] : (k1_xboole_0 = X1 | ~r2_hidden(X1,k2_relat_1(X0)))) & v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,negated_conjecture,(
% 0.20/0.53    ~! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> ! [X1] : (r2_hidden(X1,k2_relat_1(X0)) => k1_xboole_0 = X1)))),
% 0.20/0.53    inference(negated_conjecture,[],[f17])).
% 0.20/0.53  fof(f17,conjecture,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> ! [X1] : (r2_hidden(X1,k2_relat_1(X0)) => k1_xboole_0 = X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_relat_1)).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    ~spl3_2 | ~spl3_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f24,f78,f70])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    k1_xboole_0 != sK1 | ~v3_relat_1(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    spl3_2 | spl3_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f25,f74,f70])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK0)) | k1_xboole_0 = X1 | v3_relat_1(sK0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    spl3_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f26,f65])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    v1_relat_1(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (5602)------------------------------
% 0.20/0.53  % (5602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (5602)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (5602)Memory used [KB]: 10874
% 0.20/0.53  % (5602)Time elapsed: 0.113 s
% 0.20/0.53  % (5602)------------------------------
% 0.20/0.53  % (5602)------------------------------
% 0.20/0.53  % (5585)Success in time 0.173 s
%------------------------------------------------------------------------------
